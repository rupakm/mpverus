# Verifying message-passing protocols in Rust, with Verus

Reduce a concurrent system of threads communicating over channels to sequential
verification of each thread, using Lipton reduction, yield invariants and
layered refinement — the Civl techniques — embedded in Verus.

`docs/movers.pdf` is the write-up; `docs/proving.md` is a working guide for
anyone extending the proofs. It starts from a two-phase commit
implementation an engineer might write and introduces the proof ideas in order.

## Layout

    src/tok.rs        the library: channel names, `NetInv` (the interface a
                      protocol implements), `NetSM` (the one network state
                      machine, shared by every protocol), the trusted
                      primitives, and the verified operations
                      (`rpc`, `mint`, `recv_learn`, `recv_any`)
    src/proc.rs       the programming model: `Out`/`In` endpoints that own
                      their channel tokens, `Inbox` for a service waiting on
                      many peers, `Out::call` for a remote call, `open_channel`,
                      and the `Process` trait every example implements
    src/layer.rs      layered refinement: `Spec`, `Refines`, and `Layered` /
                      `BottomLayer`, which derive a refinement stack's bottom
                      from the protocol rather than restating it
    src/examples/     protocols written against the library
    counterexamples/  protocols that MUST fail to verify
    attic/            the pre-token framework, superseded; see attic/README.md
    spike/            standalone experiments cited by docs/plan.md

### Examples

| module | what it shows |
|---|---|
| `pingpong.rs` | the smallest protocol, and the one the write-up walks through |
| `lossy.rs` | an unreliable link; the smallest complete protocol |
| `heartbeat.rs` | sole-sender ownership across an interference point |
| `collector.rs` | many producers, one consumer, unordered delivery |
| `twophase_fanout.rs` | two-phase commit by broadcast and gather |
| `twophase.rs` | two-phase commit by remote call, with channels minted per call |
| `chang_roberts.rs` | ring leader election |
| `leaselock.rs` | a lease lock as three services — a lock server tracking lease expiry and refusing while a lease is live, a storage node fencing writes, and writers that hold a lease across many sequenced writes. Proves write serialization (not mutual exclusion), uses provenance to show a write's token was really issued, and carries a two-layer refinement proof: the implementation, which reads a clock and tracks the outstanding lease, refines an abstract server that either grants some higher lease number or refuses |
| `compose.rs` | two protocols on one thread |
| `multithread.rs` | one process, several threads |
| `layers_demo.rs` | refinement up to an abstract model |
| `system.rs` | **assembling a running system**: where the instance and every token come from, and how they reach the threads |

## Build

Verus is the compiler here, not `cargo`. The sources use the `verus!` macro and
depend on `vstd`, which ships with the Verus toolchain rather than crates.io, so
`cargo build` does not apply — `Cargo.toml` fixes the package's identity and
layout, and Verus does the work.

Install [Verus](https://github.com/verus-lang/verus), then:

```
VERUS=/path/to/verus ./verify.sh          # verify everything
VERUS=/path/to/verus ./verify.sh --run    # verify, compile, and run the demo
```

`verify.sh` looks in `./tools/verus-<arch>/verus` by default, so a toolchain
unpacked there needs no `VERUS`. It checks three things: the development, the
counterexamples (each of which must be rejected, and in the right way), and the
spikes under `spike/` — design experiments that verify but are deliberately not
integrated.

Currently 267 verified, 0 errors, no `assume` or `admit`. CI runs the same
script on a pinned Verus version.

See [CONTRIBUTING.md](CONTRIBUTING.md) before changing anything, and
[docs/proving.md](docs/proving.md) before writing proofs — it holds the rules
that cost real time to find.

`verus --compile` builds a running binary from the same source, and
`examples/lease_system.rs` boots the lease lock, runs its three services on
three threads, and reports the result through the endpoint API.

Two things are proof-level and do not run: `rpc` / `absorb_handler` /
`recv_abs`, which consume the reply channel's send token at the call site so no
handler can ever send the reply; and `twophase.rs`, which is built on them. The
runnable two-phase commit is `twophase_fanout.rs`.

Each counterexample declares how it must fail — `MUST FAIL TO VERIFY` or
`MUST FAIL TO COMPILE`, the latter for properties ownership enforces — and may
pin the diagnostic with `EXPECT-ERROR`. A file that fails for an unrelated
reason counts as a failure of the suite, not a pass.

## Writing a protocol

1. Declare the message type and the protocol's parameters (`uninterp spec fn`).
2. Write each participant as a struct holding its `Out`/`In` endpoints and its
   local state, with its activities as ordinary methods and its invariant as
   `Process::wf`. Activity bodies carry no ghost arguments.
3. Implement `NetInv`: the send gate, the guarantee about a message that was
   sent, the delivery discipline, and — only for a guarantee that no single
   message can express — the `history_inv` invariant and its three lemmas.
4. Write the protocol as ordinary sequential Rust, using the library's `send`
   and `recv`, passing the state machine instance and the relevant channel
   token.
5. Implement `DetDelivery` if the protocol makes remote calls, and `Layered` if
   it is to sit at the bottom of a refinement stack. Channels can be created at
   run time with `mint` without opting in to anything.

There are no mover annotations, footprints, commutativity obligations, or
descriptions of what other threads may do.

## What is assumed

Nine `external_body` declarations:

- `send_general`, `recv`, `recv_any` — the channel primitives. Their
  specifications are the state machine's transitions; `send` and `send_caused`
  are verified wrappers, not further assumptions.
- `make_endpoints` — creates a channel. It takes the channel's send and receive
  tokens and hands them straight back, which makes it callable at most once per
  channel: the machine holds exactly one of each.
- `abort_on_panicked_child` — diverges.
- four per-protocol configuration facts: how many participants, nodes or
  producers exist, and that ring node identifiers are distinct.

These now have real bodies over `std::sync::mpsc` rather than `unimplemented!()`,
so `verus --compile` produces a running program from the same source it checks.
What is trusted is unchanged in kind, but it is now reviewable code rather than
a placeholder. Two further `external_body` items are not assumptions about
behaviour: `ExMpscSender` and `ExMpscReceiver` merely tell Verus that two `std`
types are opaque.

Plus Lipton's theorem itself, which cannot be stated without an execution
semantics inside the program. Its side conditions are discharged.

Channel freshness, channel distinctness, the rule for executing a handler at the
call site, dividing ownership across threads, and the abstracted receive were
all assumptions in an earlier version of this development and are now proved.
