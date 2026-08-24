# Plan: verifying message-passing Rust against a network model

Status: proposal, for review. Nothing here is implemented.

## Goal

Verify Rust protocol implementations written against a *trusted* messaging
library, using Civl's techniques — reduction, yield invariants, layered
refinement, and the gate/action split — with Leslie models serving as abstract
specifications. Reuse Verus's tokenized state machines where they fit; build our
own where they do not.

## Where we are

116 verified obligations, 0 errors. Four pillars reviewed:

| Pillar | State |
|---|---|
| Reduction | Holds. One over-constraint (per-send invariant) found and removed. |
| Yield invariants | Holds. Cannot relate local and network state; parameterization is faked. |
| Gate/action split | Modeled correctly, but disconnected from code except via `Handler`/`rpc`. |
| Layers | **Broken.** No state abstraction, therefore no stuttering. |

Trusted today: five network primitives, `absorb_handler`, `split_token`,
`merge_token`, pool completeness, per-protocol config axioms.

## Two architectural decisions

### 1. Tokenized state machines: yes for ownership, no for invariants

TSM is a good fit for the **network model and ownership**, and a bad fit for the
**reduction and invariant layer**. The division is sharp and worth stating
plainly, because it determines everything else.

**Why it fits ownership.** The five clauses of `env_step` are all statements
about who may touch what. Each becomes a token fact:

| `env_step` clause | Token form |
|---|---|
| send histories only grow | persistent tokens never expire |
| unique sender ⇒ nobody else appends | exclusive `sent` token for that channel |
| unique consumer ⇒ nobody else consumes | exclusive `recvd` token for that channel |
| others' `recvd` may grow | you don't hold it; nothing to say |
| domain only grows | persistent channel-exists token |

So `env_step` disappears as an explicit predicate, and with it the obligation to
re-derive facts through it at every interference point. `lemma_frame` and both
`lemma_local_*` go too: you cannot write a channel whose token you do not hold,
and an unrelated append cannot affect a channel whose token you do. That is the
single largest reduction in per-protocol boilerplate available to us, and it
makes implementations *less* constrained rather than more.

`split_token` and `merge_token` also become generated, proven operations rather
than axioms, because set-sharded fields split and join by construction.

**Invariants: revised after building `spike/example_vote.rs`.** I first argued
the yield invariant could not live in the state machine, because TSM checks
`#[invariant]` per *transition* while reduction needs it per *reduced block*.
That was too pessimistic. It works, for a specific reason: every invariant we
actually write is over *monotone* history, and every send is *gated*. A gated
send that may only append conforming messages preserves such an invariant
step by step, so per-transition and per-block coincide.

All five invariants in the current development are of this shape — `Tpc` (trivially
`true`), `Fanout`, `Coll`, `Hb`, `Cr`. That is not luck; the ghost state was
designed to make it so. If a future invariant genuinely needs to break
transiently, the escape hatch is to state it over a derived monotone quantity.

So the yield invariant becomes `#[invariant]` on the machine, non-interference
becomes `#[inductive(...)]` and is discharged by the macro, and the gate becomes
a `require` inside the transition — Civl's ρ, checked at the call site.

**How a thread learns the invariant.** This is the piece the worked example
corrected. A receiver does not own the sender's history and cannot read it. It
does not need to: `recv` hands back a *persistent witness* that the message it
received was sent, and a `property!` block turns that witness into the
invariant's consequence.

```rust
property!{ learn_vote(c: ChanId, i: nat, m: Msg) {
    have was_sent >= set { (c, i, m) };
    require(c == pre.rsp);
    assert(m == Msg::Vote(pre.vote));      // proven from the invariant
}}
```

**This is what replaces `env_step`.** Knowledge travels with the message as a
token rather than being re-derived from a global predicate at every yield.
`recv` needs no environment-step existential and no invariant grant.

**Consequence: the machine is per-protocol.** Because the protocol invariant is
one of the machine's invariants, a single generic `NetSM<M>` shared by all
protocols does not survive. Either each protocol generates its own machine from
a macro, or the machine takes a predicate type parameter — the
`RwLockToks<K, V, Pred: InvariantPredicate<K, V>>` pattern from `vstd/rwlock.rs`,
retired in Phase 0 and now reinstated. The worked example suggests a
per-protocol machine is the more natural shape; a macro can hide the
boilerplate (Phase 4).

**Sharding follows the channel model.** The apparent difficulty — `sent` being
both monotone and shared — dissolves, because the two cases never overlap. FIFO
already requires a unique sender, so its send history is exclusively owned and
exactly known. Bag has many senders, but nobody needs the exact history: the
only facts any bag protocol uses are "everything ever sent satisfies P" and
"what I received was sent", both of which are monotone knowledge.

| Model | Send side | Receive side |
|---|---|---|
| `LossyBag` | persistent "was sent" facts | nothing |
| `Bag` | persistent "was sent" facts | exclusive `recvd` |
| `Fifo` | **exclusive** `sent` (unique sender) | exclusive `recvd` |

Verified against the code: `collector.rs`, the only `Bag` protocol, uses exactly
the invariant "everything on the hub is good" plus `lemma_delivered_was_sent`,
and counts nothing. `LossyBag` already destroys counting by construction. If a
future bag protocol needs to count, it must re-establish the count itself, which
is the honest outcome.

This also explains why FIFO is the strong model: it is the only one needing an
exclusive send-side token, which *is* the unique-sender requirement.

### 2. Layers get a state map, and the abstract state is arbitrary

`Refines` becomes:

```rust
pub trait Refines<Lo: Protocol, Hi: Protocol> {
    spec fn abs_state(s: Lo::S) -> Hi::S;
    spec fn abs_act(a: Lo::A) -> Option<Hi::A>;   // None: this action refines skip

    proof fn lemma_inv(s: Lo::S) requires Lo::inv(s) ensures Hi::inv(abs_state(s));
    proof fn lemma_gate(...);                      // Hi::gate ==> Lo::gate, unchanged
    proof fn lemma_step(a, req, resp, s0, s1)
        requires Lo::step(a, req, resp, s0, s1), /* Hi gate */
        ensures  match abs_act(a) {
            Some(h) => Hi::step(h, .., abs_state(s0), abs_state(s1)),
            None    => abs_state(s1) == abs_state(s0),
        };
}
```

This requires generalizing `Protocol` from a fixed `Net<M>` to an associated
state type `S`, with the bottom layer using `S = Net<M>`. Three things follow:

- **Stuttering.** Internal steps can refine skip, which is most of the point of
  having layers.
- **Different message types across layers**, which also unblocks composing
  protocols that do not share a message type.
- **Leslie models become usable directly.** `abs_state: Net<Msg> → TCommitState`
  recovers each resource manager's status from the message history. This is an
  ordinary refinement mapping. *Correction to an earlier claim: Leslie does not
  need a new network-shaped layer. The blocker was in `layer.rs`.*

## Worked example: `spike/example_vote.rs` and `spike/example_rpc.rs`

One coordinator, one participant, safety property *commit only if the vote was
yes*. 209 and 279 lines; 8 and 11 verified, 0 errors. Built to test the design
before committing to it, and it changed the design twice (above).

Absent from these files, by grep: `env_step`, `lemma_frame`, `lemma_local_*`,
`lemma_commutes`, `impl Protocol`, `Net`. The sharding discharges all of it.

**Reduction.** The participant is `recv; send` = R·L: one atomic block, one
interference point, not two. What makes `send` a left mover is now structural.
It does exactly two things — mutates an *exclusively owned* `sent` token that no
other thread can observe, and performs `add was_sent (union)=` on a *persistent*
field. A union-add on a persistent field commutes with every action by
construction and can only enable, never disable. So "send is a left mover" is a
property of the sharding strategy rather than a per-protocol obligation.

That yields a checkable discipline for gates: a gate preserves left-moverness
when it mentions constants, persistent fields, or fields the thread exclusively
owns. A gate mentioning another thread's *mutable* state is exactly what breaks
it — visible by reading the transition, not by proving four lemmas.

**The RPC trick survives and improves.** `send; recv` is still L·R and still
fixed by strengthening the gate until the receive cannot block. The gate is now
"the caller holds a persistent witness that the reply was sent, at the index it
is about to consume". Two things fall out:

- *Determinism for free.* The witness names the index and the machine's `agree`
  invariant pins the message. `oneshot`'s freshness requirement and
  `lemma_singleton_delivery` both disappear.
- *`absorb_handler` stops being an axiom.* The caller performs the handler's own
  transition using the reply channel's send token, which it holds because it
  minted the channel. It is a verified `proof fn`. The residual obligation —
  that the caller and the real participant do not both send the reply — moves
  from a state axiom to Rust linearity: `rpc` takes the reply capability **by
  value and consumes it**, because a reply channel is one-shot.

Trusted surface across both files: three `external_body` functions — `send`,
`recv`, `recv_abs` — whose specifications are literally the machine's
transitions. `absorb_handler` and `rpc` are verified.

**Not vacuous.** Five deliberate breakages, each rejected: participant lying
about its vote (gate), coordinator dropping `learn_vote` (safety postcondition),
coordinator permitted to write the response channel (gate), `rpc` without
index alignment (gate), absorbing the wrong reply (gate and postcondition).

## Phases

Every phase boundary must leave the whole development verifying with zero
errors and no new `assume`. Phases are ordered so that the broken pillar is
fixed first and the riskiest change is gated on a cheap experiment.

### Phase 0 — TSM feasibility spike — **DONE, GO**

Spikes in `spike/`, verified standalone (not part of `src/main.rs`):

| Spike | Question | Result |
|---|---|---|
| `s1.rs` | generic `M`, map-sharded `Map<ChanId, Seq<M>>`, `#[invariant]` + `#[inductive]` | 4 verified |
| `s2.rs` | `persistent_set` for monotone "was sent", duplicable via `.clone()` | 2 verified |
| `s3.rs` | `split_token` / `merge_token` as *proved* operations | 1 verified |
| `s4.rs` | `Spec` / `Protocol` trait split, stuttering, Leslie-shaped abstract state | 2 verified |

`s3.rs` is the one that matters most: `SetToken::remove` / `insert` give fork and
join of endpoint ownership with disjointness holding structurally, replacing two
axioms with proved code.

Two findings that change the plan:

- ~~**The predicate type parameter is not needed.**~~ *Reversed by the worked
  example:* the protocol invariant does belong in the machine, so the machine is
  protocol-specific. Either a macro generates one per protocol, or the
  `rwlock.rs` predicate-parameter pattern comes back.
- **The fallback is not needed.** The macro handled generics, `Seq`-valued map
  sharding, persistent sets and generic inductive proofs without complaint.

### Phase 1 — Layers — **DONE**

**115 verified, 0 errors** (was 109). Counterexamples still rejected, now for
the right reason (see below).

Delivered:

- `Spec` introduced in `api.rs`: `type S / A / M`, `inv`, `gate`, `step`.
  `Protocol : Spec<S = Net<M>>` keeps `type C`, `footprint`,
  `lemma_recv_preserves` and the mover obligations. Every protocol's single
  `impl` became two, split along a line already visible in the file.
- `layer.rs` rewritten. `Refines<Lo: Spec, Hi: Spec>` with `abs_state`,
  `abs_act -> Option<Hi::A>` and `abs_msg`; the two layers may now differ in
  state, actions and messages. New `lift_stutter`; `refines_trans` and
  `inv_trans` generalized, with `abs_act2` composing two abstraction maps so an
  action invisible at *either* step is invisible at the top.
- `CrRefines` migrated (identity mapping, every action visible).
- **2PC now has a layer**, `TpcAbs`, whose state is `Tally { yes: ISet<ChanId> }`
  — not a network. `abs_state` recovers it from the message history. This is the
  Abadi–Lamport mapping shape that Phase 5 needs, rehearsed on a protocol we
  already have.
- `TpcAct::Local`, an internal step touching no channel, maps to `None` and is
  absorbed into stuttering. `tpc_layer_demo` and `tpc_stutter_demo` exercise
  both branches.

**Negative test.** Declaring `Prepare` invisible too (`abs_act(Prepare) = None`)
fails the postcondition, so the stuttering branch is not vacuous.

**A limitation found while building it.** `abs_act` is a function of the action
alone, so an action cannot be invisible in some states and visible in others.
That is the right design: state-dependent visibility belongs on the `Hi::step`
side, where the abstract transition simply admits `s1 == s0`. `None` is for
actions that are *always* internal.

**A near-miss worth recording.** After the trait split the counterexamples
stopped *compiling*, and `check.sh` — which only tested for a non-zero exit
code — reported them as correctly rejected. The suite was green while testing
nothing. `check.sh` now insists on a real verification verdict with a non-zero
error count, and refusing to reach verification is itself a failure. Verified by
deliberately breaking a counterexample's syntax and confirming the suite goes
red.

### Phase 2 — Network on tokens — **DONE**

Module order chosen so ownership is stressed first: `heartbeat` (done) →
`twophase` → `twophase_fanout` → `collector` → `chang_roberts` → `multithread`
→ `compose`.

**`src/tok.rs`: the generic seam.** Each protocol needs its own state machine,
because its yield invariant is one of that machine's invariants. Left alone that
would force a per-protocol trusted `send`/`recv`. `ChanTokens` fixes it: the
machine exposes its token types, readers for them, its send gate, and two proof
methods that perform its own transitions in ghost. Above that sit ONE trusted
`send`, ONE trusted `recv`, ONE trusted `recv_abs`, and `interference_point`.

The deciding argument was ergonomic rather than about the trust boundary. A
macro can generate a per-protocol seam just as easily as a per-protocol trait
impl, so on typing-per-protocol the two options tie. What the trait adds is
**protocol-generic verified combinators** — `rpc`, broadcast, gather, fork/join
— written once as a library instead of regenerated per protocol. `rpc` is
already such a combinator today; losing its genericity would have been a real
regression. `send_exchange` is the method that makes `absorb_handler`
genericizable. Validated in `spike/s5.rs` (36 verified), including a generic
combinator over the trait.

**`heartbeat` ported.** It was chosen first because it leans hardest on
ownership: a sole sender must still know, after an interference point, exactly
what it wrote. Results:

| | before | after |
|---|---|---|
| proof obligations in the module | 11 | 4 |
| proof after the yield | 3 assertions | *empty* |
| `env_step` | required and re-analysed | gone |
| trusted functions | 1 generic pair, shared | same, still shared |

`yield_point` — generic over the protocol, taking the token, requiring the
invariant, returning an `env_step` existential — collapsed to
`interference_point()`, which takes nothing and promises nothing. The facts a
thread needs are in tokens nobody else can hold, so there is nothing to
re-establish.

Negative tests bite: dropping the gate obligation fails a precondition,
strengthening the postcondition beyond what ownership gives fails.

**A wrinkle worth recording.** `ChanTokens` requires both a send and a receive
side, and `HbSM` originally modelled only sending. Rather than split the trait,
`recvd` and `do_recv` were added to the machine — the link does have a reader;
we simply had not modelled it. If a protocol ever genuinely has no receive side,
split the trait rather than fake one.

**The trait shrank.** Generated tokens implement vstd's `KeyValueToken` /
`ElementToken`, so eight reader spec functions collapsed into two trait bounds.
A protocol's impl is now one `inst_id`, the gate, and two exchange delegations.
`MapToken` also comes for free, which is how a coordinator holds one token per
channel.

**Layering over a machine's state: answered, by `spike/s6.rs` (41 verified).**
`Spec::S = HbSM::State` works for the bottom layer, and the layer above it uses
`(nat, u64)` — not a state machine state at all. Stuttering works across it.

That spike also found a gap in `layer.rs`: `lemma_gate` and `lemma_step` could
not assume the concrete invariant, but Civl checks refinement only at reachable
states. In the spike the abstraction kept only the last sequence number while
the concrete gate spoke of every element, and bridging the two *requires* the
`increasing` invariant. Fixed: both lemmas, and `lift` / `lift_stutter` /
`refines_trans`, now carry `Lo::inv`.

**`twophase_fanout` ported** — chosen over `twophase` as the second module
because it has no dependents, uses static channels (so it sidesteps allocation),
and exercises the two things heartbeat could not: a loop over many channels, and
a receiver learning from the yield invariant rather than from a handler.

The coordinator holds `MapToken`s over its request and reply channels and moves
a single-channel token in and out around each operation. The collect loop cashes
in the invariant with the machine's `learn_vote` property, using the witness
`recv` hands back. Proof/spec functions 19 → 15; length unchanged at ~308 lines.
Negative tests bite: a participant voting `true` regardless fails the gate;
dropping `learn_vote` fails the loop invariant.

**Generic combinators landed — the payoff the trait was chosen for.**
`absorb_handler` and `rpc` are now written ONCE in `tok.rs`, against
`ChanTokens`, and verify generically with no protocol instantiated.
`absorb_handler` is a `proof fn`, not `external_body`: it left the trust
boundary when the model did.

**The recv side generalized across disciplines.** `ChanTokens` gained
`type RecvdVal`, `deliverable_at(v, i)` and `after_recv(v, e)`. FIFO says
`i == v.len()`; other disciplines say something else. One trait, no split.

**`collector` ported, and it forced a modelling change worth recording.** The
old version had one `Bag` channel with many senders and `dup`ed capabilities.
That does not survive tokens, and the reason is structural rather than
incidental: **a single send history with several concurrent appenders cannot be
exclusively owned, and without exclusive ownership `send` is not a left mover.**
The old model paid for many senders by discarding order entirely.

A bag is therefore now a FAMILY of per-producer channels. Each producer
exclusively owns its own history, so ownership and left-moverness are restored,
and per-producer order is kept — which real `mpsc` also keeps, and which the old
`Bag` model threw away. "Any order" moves to the receive side, as `recv_any`, a
single generic trusted primitive that blocks on a family of channels and reports
which one fired.

Consequence: `Sender::dup` is no longer needed or wanted.

**Unreliable networks: kept.** I briefly recorded `LossyBag` as possibly lost in
this move. That was wrong, and the error is worth naming because it is easy to
repeat. Two things are independent:

- **Who may send** decides whether `sent` is exclusively owned, and hence
  whether `send` is a left mover. Many senders force a family of channels.
- **The delivery discipline** decides what a receiver may be handed. It is
  purely receive-side: `deliverable_at` and `after_recv`.

Unreliability is the second kind. A lossy link has one sender and one receiver —
it is a datagram link, not a shared mailbox — so ownership is untouched.
`src/lossy.rs` carries it over, and the entire difference from FIFO is one line:

```rust
open spec fn deliverable_at(v: Seq<Pkt>, i: nat) -> bool { true }
```

Loss still needs no modelling: nothing forces a delivery, so a message that
never arrives leaves the receiver blocked. Duplication is expressed by dropping
the index constraint, and the persistent witness is what makes re-delivery
expressible at all — a witness is duplicable and never retracted, so handing the
same one back twice is exactly what a duplicating network does.

What survives verbatim: "everything ever sent satisfies P", and the bridge from
a delivered message back to the send history. Both are statements about the send
history, which duplication and loss do not touch.

What is lost, provably: counting. `two_are_distinct` in `src/heartbeat.rs`
proves that two FIFO receives come from two distinct sends;
`counterexamples/lossy_counting.rs` makes the identical claim on a lossy link
and is rejected. Same source shape, one line of difference. A protocol that
needs the count must re-establish it with sequence numbers in the message, which
is the honest outcome.

Negative tests bite on every ported module.

**The learn seam, and a fact it made obvious.** `ChanTokens` gained
`wit_inv(c, m)` -- what the yield invariant says about a message that was sent
-- and `proof fn learn(inst, w)`, which cashes it in from a witness. That is the
seam that lets GENERIC code use a protocol's yield invariant; without it every
combinator in `tok.rs` was limited to what ownership alone proves.

Building it surfaced something worth stating: **for five of the six protocols
the yield invariant IS the send gate, remembered.** Compare, in each case, the
gate on a send with what the invariant says about a message already sent -- they
are the same predicate. So `chan_protocol!` now takes one `wit_inv` declaration
and generates the machine's yield invariant, its `learn` property, the trait's
two new members, AND the invariant-preservation half of `do_send_inductive`.
Each protocol's `send_preserves` collapsed to `{ }`.

`heartbeat` is the exception, and instructively so: its invariant is about PAIRS
of messages (each beat's number exceeds the previous), so a single witness says
nothing. Its `wit_inv` is `true` and `increasing` stays hand-written.

`recv_learn` in `tok.rs` bundles receive-then-learn, which is what nearly every
protocol was writing at every receive.

Negative test: weakening a protocol's gate so it no longer implies its own yield
invariant fails inside the generated inductive proof. The gate and the invariant
cannot drift apart.

**Channel distinctness is a theorem, not an axiom.** `ChanId` is now a datatype
-- a family tag plus a sequence of indices -- built by `chan(fam, ix)` in
`tok.rs`, with `lemma_chan_inj1` / `lemma_chan_inj2` proving injectivity once.

Protocols define their channel names concretely (`req_chan(j) = chan(0, seq![j])`,
`rsp_chan(j, k) = chan(1, seq![j, k as int])`) instead of leaving them
uninterpreted, so everything that used to be assumed about them is now derived:
participants have distinct channels, a request channel is never a reply channel,
and `rsp_chan` is injective in BOTH the owner and the call counter -- the last
being what makes a dynamically minted channel gateable by its owner, and what
makes allocation fresh.

Each `config()` is now a VERIFIED proof function that calls one small axiom.
What is still assumed, in full:

| axiom | content |
|---|---|
| `twophase::n_parts_nonneg` | `n_parts() >= 0` |
| `twophase_fanout::n_parts_nonneg` | `n_parts() >= 0` |
| `collector::n_producers_pos` | `n_producers() > 0` |
| `chang_roberts::ring_config` | `n_nodes() >= 1`, and node ids are distinct |

That is the whole per-protocol residue, and none of it is about channels any
more: it is how many participants exist and whether their identities are
distinct, which really are facts about the deployment.

Negative test: giving requests and replies the same family tag fails
`config()`'s postcondition, so the distinctness is genuinely proved rather than
restated.

**`chan_protocol!` generates the machine skeleton and the `ChanTokens` impl.**
Five of the six protocols now declare only what is actually theirs -- message
type, delivery discipline, send gate, yield invariant, and the proof that a send
preserves it. The three sharded fields, the `agree` invariant, `boot`,
`do_send`, `do_recv`, the two inductive stubs and all five `ChanTokens` members
are emitted.

The generated `do_recv` takes the index as a transition argument and gates it
with `deliverable_at`, so the delivery discipline is a parameter rather than
baked in: FIFO pins the index to the current length, an unreliable link allows
any, repeatedly. That is what let `lossy.rs` go through the same macro as the
others.

| module | lines before | after |
|---|---|---|
| `heartbeat` | 224 | 157 |
| `lossy` | 206 | 139 |
| `collector` | 196 | 131 |
| `twophase_fanout` | 298 | 229 |
| `chang_roberts` | 323 | 266 |
| `twophase` | 312 | 312 (hand-written) |

Three things came out of building it that are worth keeping in mind.

*Verus syntax cannot be captured as `:block` or `:expr`.* `==>` is not Rust, so
every protocol-supplied fragment is a `tt` slurp.

*Macro hygiene severs `pre` and `post`.* Those bindings are introduced by the
inner proc macro, so a caller-written identifier does not unify with them.
`send_preserves` works around it by naming the binders itself and aliasing the
caller's names with `let`. That trick does not generalize to an `#[inductive]`
for an EXTRA transition, which is why `twophase.rs` -- the one protocol with an
allocator transition -- is still written out by hand. Documented on the macro.

*Sharded constants are better as module-level `uninterp` functions.*
`heartbeat` and `lossy` had `#[sharding(constant)] link`, which forced their
gates and properties to read `pre.link` -- straight into the hygiene problem.
Moving to `pub uninterp spec fn link()` fixed it and made them uniform with the
four protocols that already worked that way.

Negative test: making `gate_state` and `gate_inst` disagree fails
`send_exchange`, so the two forms of the gate cannot drift.

**The bottom layer is derived, not hand-copied.** `layers_demo.rs` used to
restate the protocol's gate and transition as `HbBot`, so refinement was proved
about a *copy* with nothing checking the copy agreed with the protocol the
tokens verify.

`Layered : ChanTokens` (opt-in, since layering is optional) has a protocol name
its machine's own state, invariant, and transition relations -- one line each,
pointing at what `tokenized_state_machine!` already generated -- plus one
coherence lemma, `lemma_send_gate_st`, tying the state-level gate to the
machine's own `require`. `BottomLayer<T>` is then `Spec` derived from those, so
there is no second definition to drift.

Confirmed to be real by two breakages: claiming a state gate the machine does
not enforce fails `lemma_send_gate_st`, and *weakening the machine's own gate*
fails the layer proof. The refinement now tracks the protocol rather than a
paraphrase of it.

A modelling point fell out. `abs_act` is a function of the action alone, so
`Send(c)` cannot be visible for `c == link` and invisible otherwise. The
abstract transition absorbs it instead: `HbTop::step` is
`(count grows) || (state unchanged)`. State-DEPENDENT stuttering belongs on the
`Hi::step` side; `None` is for actions that are always internal, which is what
`Recv` is here.

**`recv_abs` is verified, and RPC now says out loud what it needs.**
`DetDelivery : ChanTokens` supplies two facts -- at most one index is
deliverable, and witnesses naming the same slot name the same message (read off
the machine's `agree` invariant). `recv_abs` is `recv` plus those two, and `rpc`
requires `DetDelivery`.

The point is not just one axiom fewer. `lossy.rs` **cannot** implement
`DetDelivery` -- `lemma_delivery_determined` fails, as it must, since an
unreliable link may hand back any index at any time. So "RPC needs deterministic
delivery" went from an invisible assumption inside a trusted spec to a trait
bound the compiler enforces.

`interference_point` also stopped being `external_body`: an empty body with no
specification has nothing in it to trust.

**Channel allocation costs no per-protocol axiom.** `ChanAlloc : ChanTokens` in
`tok.rs` carries the ghost side -- `alloc_count`, `chan_of`, and a
`alloc_exchange` verified per protocol by delegating to the machine's own
`alloc` transition. `mint<T: ChanAlloc>` is a VERIFIED generic function. The
only trusted part left is `make_endpoints`, which fabricates two handles for a
channel id, touches no ghost state, and is protocol-independent. `twophase.rs`
is back to one `external_body` (its configuration axiom).

**`twophase` ported, with dynamic channel allocation, and `oneshot`'s freshness
axiom retired.** The allocator is an exclusively-owned counter
(`#[sharding(variable)] next`) plus an invariant that nothing at or above it is
allocated:

```rust
#[invariant] pub spec fn unallocated(&self) -> bool {
    forall|j: int, k: nat| k >= self.next
        ==> !self.sent.dom().contains(#[trigger] rsp_chan(j, k)) && ...
}
```

Minting a channel adds a key to a map-sharded field, which carries an *inherent
safety condition* — the key must be absent. That is discharged from the
invariant. Confirmed to be real by weakening the invariant, which produces
"unable to prove inherent safety condition: the given key must be absent from
the map before the update". So `oneshot`'s specification no longer claims
freshness at all: it is the machine's business, proved rather than assumed.

**Owner-tagged reply channels.** A dynamically minted channel has no static
identity, so the send gate cannot name it. Encoding the owner in the id --
`rsp_chan(j, k)` for participant `j`'s `k`-th call -- makes the gate a pure
function of the channel:

```rust
pub open spec fn reply_ok(c: ChanId, m: Msg) -> bool {
    forall|j: int, k: nat| c == #[trigger] rsp_chan(j, k) ==> m == Msg::Vote(vote(j))
}
```

No auxiliary ownership map, and no `birds_eye` into untokenized state.

**The generic `rpc` has its first client.** Each loop iteration mints a reply
channel and makes one remote call which, being `L . L`, contains no interference
point; the coordinator's loop is a plain sequential loop invariant. Both
`twophase` (learning by absorbing the handler) and `twophase_fanout` (learning
from the yield invariant) prove the same safety property by different routes.

Negative tests bite: absorbing a reply of the coordinator's own choosing fails
the gate; dropping `rsp_chan` injectivity fails both the gate and freshness.

**`compose` and `multithread` were retargeted at `src/twophase_legacy.rs`**,
which retains the old `Protocol`-based two-phase commit. They are not ported —
composition of two state machines is a different design problem from composing
two `Protocol` impls, and token splitting for sibling threads should reuse
`MapToken` rather than `split_token`/`merge_token`. Both still verify against the
old framework, so nothing was lost, but they are pending re-expression.

**`chang_roberts` ported.** About 170 lines of mover lemmas deleted -- footprint,
framing, two locality lemmas, commutation -- plus the `env_step` reasoning at
the receive, which became one `learn_msg_ok` call on the witness. The ring
arithmetic (`lemma_full_circle`, `lemma_covers`) carried over untouched, as it
should: that is about ids, not about the framework.

**`compose` collapsed to nothing.** The old module was 350 lines: a `Sum` action
type, a `Compatible` trait with four cross-cutting obligations, and
`Both<P, Q, X>`. All of it existed because ONE global `Net` was shared by every
protocol. Under tokens each protocol is its own instance -- separate ghost state
-- so non-interference between protocols is structural, not proved. What
replaces `Compatible` is a modelling rule: *if two protocols share a channel,
they are one state machine*, because a channel's token belongs to one instance.

**`multithread` lost its axioms.** `MapToken::remove` / `insert` are proved vstd
operations and disjointness holds by construction, so `split_token` and
`merge_token` are gone.

**`net.rs`, `api.rs` and `twophase_legacy.rs` moved to `attic/`**, with
`attic/README.md` recording what each was and what replaced it.

**The counterexamples are the clearest measure of the change.**
`nonlocal_gate.rs` and `understated_footprint.rs` are now in the attic because
they are *no longer expressible*: a gate is handed only the channel it is about,
so it cannot read another channel's state, and there are no footprints because a
thread can only write a channel whose token it holds. The token model makes
those mistakes unrepresentable rather than checkable. What is still worth
catching is the gate, and `counterexamples/dishonest_participant.rs` does that.

**Obligation count 119 -> 76.** That is the attic move, not a regression:
`net.rs`'s three `ChannelModel` instances alone were ~24 proof functions, all
superseded by one line of `deliverable_at` per discipline.

Axioms retired across Phase 2: `split_token`, `merge_token`, `absorb_handler`,
and `oneshot`'s freshness postcondition.

**Still open, and moved to Phase 3:** `cr_step` lost its refinement
postcondition (`exists n_pre. gate && step`) in the port. Connecting a function
BODY to a declared action needs the global state that tokens deliberately hide.
That is exactly the attribution problem Phase 3 exists to solve.

**Exit:** three axioms (`split_token`, `merge_token`, `absorb_handler`) and
three per-protocol obligations gone, all modules green.

### Phase 2b — Assembling a system — **DONE**

Every component was verified under preconditions --- it holds an instance, it
holds a particular channel's token, its endpoints name the channels it expects
--- and nothing discharged them. `fn main()` was empty and no `Instance` was
ever constructed. Two components with jointly unsatisfiable preconditions would
each still have verified.

`src/examples/system.rs` is the wiring, and it answers where the proof state
comes from:

- `Instance::boot(chans)` is called once and returns the instance together with
  **every token in the system**: one send token and one consumption token per
  channel, plus the initially empty witness set. No token originates anywhere
  else, except `mint`, which creates a channel and its tokens together.
- `make_endpoints` creates each channel's two handles; which thread gets which
  is a decision of the assembly code, not of the library.
- The token maps are divided by removing what a participant needs; what remains
  belongs to the coordinator. Because tokens cannot be copied, the division is
  disjoint and exhaustive by construction, and that is what makes the
  components' ownership assumptions simultaneously true.

The safety property is now stated about a system that exists rather than about a
component in isolation. Three deliberate miswirings are rejected: handing a
participant the wrong channel's token, omitting a channel from the system, and
failing to relate a participant's vote to the protocol's.

This also forced a real improvement to a component: `coordinator_fanout` did not
say what became of the token maps it borrowed, so a caller could not put them
back. Components must describe what they return, not only what they require.

Remaining: the deployment is two participants written out. An arbitrary size
needs the endpoint construction and token division in loops, which is
mechanical. And `deployment_size` is a new assumption --- an honest one, being a
fact about a deployment rather than about the protocol.

### Phase 3 — Connecting code to actions — **OPEN, and the main gap**

Originally stated as "attribute every network operation to a declared action".
Half of that is now enforced by construction rather than checked: a thread can
touch only channels whose tokens it holds, and every send goes through the
machine's own transition with its gate. What remains is the other half, and it
is a real gap.

Nothing currently states that *a particular Rust function body performs one step
of a declared abstract action*. Before the move to tokens, `cr_step` carried a
postcondition of the form

```rust
exists|n_pre| Cr::inv(n_pre) && Cr::gate(a, req, n_pre)
           && Cr::step(a, req, resp, n_pre, final(t).net)
```

which is Civl's condition that along every path there is exactly one
yield-to-yield fragment behaving like the refined action. It was dropped in the
port because it needs the global state that the token representation
deliberately hides: a thread holds tokens for its own channels and cannot speak
about the machine's whole state.

`Layered` / `BottomLayer` did the *specification* half of the reconnection — the
bottom of a refinement stack is now derived from the protocol rather than
restated. What is missing is the *code* half: a combinator, along the lines of

```rust
atomic::<T>(a, req, tokens, |tokens| { ... })
```

whose postcondition is "this body performed `BottomLayer::<T>::step(a, ...)`".
Without it, a refinement chain proves things about the protocol's transition
system but nothing ties a running function to it, so Phases 5 and 6 would
connect a Leslie model to a specification rather than to code.

Two possible approaches:

- Have the trusted primitives accumulate a ghost record of the operations a
  thread performed since its last interference point, and have the combinator
  check that record against the declared action. Costs a ghost field on every
  token operation.
- Express the step over the *tokens the thread holds* rather than over the whole
  state, which is closer to how `BottomLayer` already works, and requires
  `Spec::S` to be instantiable at a partial state.

The second looks more in keeping with the rest of the design and has not been
tried.

### Phase 4 — Ergonomics — **DONE**

The original text described blanket implementations for framing and
commutation. Those obligations no longer exist, so that part is moot.

What was done instead, after `chan_protocol!` was abandoned (see "Two
architectural decisions"): ONE state machine, `NetSM`, parameterised by a
protocol's `NetInv` implementation, plus `proc.rs` -- endpoints that own their
tokens, `Inbox`, `Out::call`, and the `Process` trait. A protocol writes no
state machine and its activity bodies carry no ghost arguments.

**Exit met:** a protocol supplies its message type, delivery discipline, gate,
guarantee about sent messages, and — only when the guarantee is not the gate
restated — the preservation proof.

### Phase 5 — Leslie bridge

- Export Leslie's lowest `ActionSpec` as data: action names, gates, transitions,
  invariant. `GatedAction { gate, transition }` already matches our
  `(gate, step)` pair.
- Generator emits the top-layer Verus `Protocol`. The generator is trusted; the
  hand transcription it replaces is not reviewable.
- Round-trip test: generated spec re-exported and compared.

**Exit:** one Leslie model is the top of a verified refinement chain.

### Phase 6 — Pilot end to end

**Chandy–Lamport snapshots.** Genuinely asynchronous, *requires* per-link FIFO
(which nothing currently exercises non-trivially), the marker rule is a clean
`R* · N · L*` handler, and it needs no quorum — so it avoids the inductive
sequentialization gap. Leslie already has it.

**Exit:** Rust implementation, refinement to the Leslie model, safety property.

## Deferred cleanups (from a four-angle review of the ported code)

Applied already: shared `agrees` / `lemma_agrees_push` / `fifo_deliverable` in
`tok.rs`, dropping `RecvdVal` and `after_recv`, dead-code and stale-comment
removal, and the `ChanAlloc` split below. These were judged design work rather
than cleanup and are left:

| item | why it matters |
|---|---|
| Derive `recv` from `recv_any` | `recv` is `recv_any` on a singleton, but the derivation needs a `Vec` of owned `Receiver`s (which are deliberately not `Clone`) and a move out of `tracked &mut` (which needs a replacement value Verus cannot fabricate). Doing it would mean a by-value token protocol at every call site -- a worse trade than one axiom whose spec is three clauses. Revisit only if all protocols move to `MapToken`s. |
| Trigger reshaping | Quadratic `config` axioms in `twophase.rs`; 4-variable invariants where one variable is determined by another (`chang_roberts`, `twophase_fanout`); an `exists` nested under a `forall` in `collector`. Real, but the whole crate verifies in under two seconds, so this is a watch-item. |

## Out of scope

- Inductive sequentialization. Needed for true quorum gathering (first *m* of
  *n*); the fan-out coordinator collects in fixed order to avoid it. Revisit
  after Phase 6.
- Shared mutable state between threads of a process outside the network.
- Verifying the messaging library itself.
- Byzantine and probabilistic protocols from Leslie.

## Trusted at the end

- `send`, `recv`, `recv_abs`. *Accepted by decision.* Their specifications are
  the state machine's transitions.
- Lipton's theorem. Irreducible without a trace semantics. (`absorb_handler` is
  no longer assumed — see the worked example.)
- Pool completeness, for threads outside this codebase only (Phase 3).
- The Leslie generator (Phase 5).
- Per-protocol configuration axioms.

## Risks

| Risk | Mitigation |
|---|---|
| ~~TSM macro fights generics~~ | Retired: `s1`–`s4` verify |
| ~~Monotone `sent` does not shard cleanly~~ | Retired: sharding follows the channel model |
| Phase 2 ripple stalls mid-way | Module-at-a-time, all-green boundaries, `heartbeat` first |
| `type S` touches every protocol | Mechanical; `S = Net<M>` default keeps diffs small |
| Leslie export format shifts | Pin a commit; keep the generator tolerant |

## Decisions taken

1. **Phase 2 goes ahead.** The gain is deleting `env_step` and five obligations
   — expressiveness and ergonomics, not soundness — and Phase 0 removed the
   execution risk.
2. **Separate `Spec` trait**, resolved by `s4.rs`. `Protocol` stays
   network-specific as a sub-trait.
3. **Phase 3 before the Leslie work**, so the pilot is written in the final
   shape rather than rewritten into it.
4. **Chandy–Lamport as pilot.** Exercises FIFO, which nothing currently does
   non-trivially, and needs no quorum.

## Protocol state in the network machine

The remaining expressiveness gap. A protocol may declare its own state machine
today, but it is an independent instance, so nothing can relate it to network
state. Three things that look separate all reduce to this:

- global monotonicity of the lease server's grants (the counter is a local
  variable nobody else can read);
- mutual exclusion rather than write serialization (needs an exclusive token);
- happens-before across channels (`was_sent` indices are per-channel, so there
  is no global order). Chandy--Lamport's consistent cut needs one.

### The shape

Two fields, following the discipline the rest of the machine already obeys: a
gate may read state that is exclusively owned, or state that is monotone.

    #[sharding(map)]            pub pstate: Map<int, Inv::P>   // owned per participant
    #[sharding(persistent_set)] pub pfacts: Set<Inv::F>        // monotone exports

with `pinit`, `pstep`, `pfact_ok` on `NetInv`, a `do_pstep` transition that
advances a participant's own state, and a `publish` transition that exports a
fact from it. `pstate` is keyed by participant for the same reason `sent` is
keyed by channel: single ownership is what makes reading it stable.

The consuming side needs no new mechanism. Generalise the evidence a send may
present from messages to anything monotone:

    enum Ev<M, F> { Sent(ChanId, nat, M), Fact(F) }

`send_general` already takes a set of evidence and `learn_cause` already reads
it back; both become generic in the evidence type. So provenance is not
superseded by protocol state --- it is the delivery mechanism for it.

### Feasibility

`spike/pstate.rs` checks the two things that could have sunk this, and both
work: a TSM field may have a protocol-supplied associated type (`Map<int,
Pr::P>`), and `have pstate >= [id => p]` reads a `map` field without consuming
it, so `publish` does not disturb the owner. 5 verified, 0 errors.

### Phases

1. Add `pstate`, `pinit`, `pstep`, `do_pstep`, with all three defaulting to a
   unit type so no existing protocol changes. Check the nine protocols still
   verify untouched.
2. Add `pfacts`, `pfact_ok`, `publish`, and `fact_inv` (what a fact witness
   guarantees), with the invariant that every published fact was licensed by
   its owner's state.
3. Generalise evidence to `Ev<M, F>`; `caused_by` and `cause_gives` follow.
   `send`, `send_caused` keep their signatures.
4. Pilot on the lease lock: server's counter becomes its `pstate`, grants
   publish `Issued(t)`, and global grant monotonicity becomes provable.
   Negative test: a server that reuses a token must fail.
5. Pilot on Chandy--Lamport, which is what will show whether per-participant
   state is the right granularity.

### Risks

Steps 1 and 2 are mechanical given the spike. Step 3 touches every use of
provenance. Step 4 is the real test: if `Issued(t)` has to say anything about
*other* participants' state, the design is wrong and the fields need rethinking
before step 5.

## Processes and channels: a service-shaped programming model

Goal: the verified artifact should be the service code, not a transcription of
it. Real services are organised as a process or service object that owns its
endpoints and exposes activities; activities send, receive, and make calls.
Today a protocol body takes the instance and every channel token as arguments,
which is the opposite of that.

### Endpoints own their tokens

The shape, since landed as `src/proc.rs`:

    pub struct Out<M, Inv: NetInv<M>> {
        pub tx:   Sender<M>,
        pub tok:  Tracked<NetSM::sent<M, Inv>>,
        pub inst: Tracked<NetSM::Instance<M, Inv>>,
    }

with `wf()` saying the token describes the channel the handle names, on the
machine it names, and `send` a method with no ghost arguments. `In` is the dual
over `recvd`. The generated `Instance` has `clone()`, so every endpoint can
carry its own handle and nothing needs threading.

### The Process interface

    pub trait Process : Sized {
        spec fn wf(&self) -> bool;
        fn step(&mut self) requires old(self).wf() ensures final(self).wf();
    }

`wf` is the yield invariant of every interference point inside `step`, and what
deployment must establish before the process first runs. Ping-pong written this
way has a body with no ghost arguments at all:

    fn step(&mut self) {
        self.req.send(Msg::Ping);
        let answer = self.rsp.recv();          // the interference point
        match answer { Msg::Pong(v) => { self.seen = v; } _ => { } }
    }

### On the macro

No new macro. The friction that killed `chan_protocol!` was `macro_rules!`
splicing into a proc macro; this layer is ordinary structs and traits over the
existing `NetSM`, and `spike/pstate.rs` shows `tokenized_state_machine!` already
accepts protocol-supplied associated types. Revisit only if something blocks.

### Interaction with protocol state

They fit together rather than competing. `pstate` is keyed by participant, and
a `Process` *is* a participant, so a process holds the token for its own slice
of `pstate` exactly as it holds its endpoints. The `wf` of the process is where
"my local variables agree with my ghost state" is stated.

### Note on trait defaults

Trait default spec bodies are not reliably visible at an impl -- a protocol
relying on the default `needs_cause` verified in one crate and failed in
another. Every protocol now states `needs_cause` explicitly. Prefer explicit
overrides to defaults anywhere the default's *body* has to be known.

### Status: process model landed

`src/proc.rs` is in the library and `src/main.rs` verifies at 120, 0 errors.
Counterexamples still rejected, no `assume`/`admit`, nine behavioural axioms.

Done:
- `Out`/`In` endpoints owning their tokens; `Process` trait; `run` driver.
- Real bodies for the primitives over `std::sync::mpsc`, so `verus --compile`
  emits a running binary from the source Verus checks. `demo()` in `main.rs`
  exercises it.
- `pingpong.rs` ported: `Responder` and `Initiator`, activity bodies with no
  ghost arguments.
- `leaselock.rs` ported: `LockServer`, `StorageNode`, `Writer`, with vectors of
  endpoints and a round-robin `step`. Provenance survives the port.
- `counterexamples/forged_lease.rs` rewritten against the new model.

Not done:
- Seven examples still in the old argument-threading style: `lossy`,
  `heartbeat`, `collector`, `twophase`, `twophase_fanout`, `chang_roberts`,
  `compose`, `multithread`, `layers_demo`. They verify; they just do not read
  like service code yet.
- `system.rs` still deploys the old-style functions. It should construct
  services and hand each its endpoints, which is where the token flow becomes
  legible.
- `movers.tex` still describes the old shape. The ping-pong and lease-lock
  sections need rewriting around services, and a subsection on the programming
  model belongs before them.
- Multi-endpoint services poll round-robin because `recv_any` has not been
  lifted to the process layer. A service that must wait on many channels at
  once needs that, and it is the obvious next piece of `proc.rs`.
- The lock server's counter saturates rather than overflowing; at saturation it
  stops issuing fresh tokens and storage refuses the writes. Safe, not live.

### Closed: the double-open gap

`make_endpoints` now takes the channel's send and receive tokens and returns
them. Since the machine holds exactly one of each, opening a channel twice is a
use-after-move rather than a proof obligation, and the two ends are paired with
each other by construction. `open_channel` and `open_new_channel` in `proc.rs`
are the verified wrappers services actually use.

Rejected the alternative -- a run-time table of bound names, TCP-style -- for
in-process channels, since ownership is stronger and costs no assumption. That
design is still the right one for a transport whose two ends live in different
processes and so have no token to pass; binding an already-bound address has to
fail at run time there.

`counterexamples/check.sh` grew a second mode for this: files may declare `MUST
FAIL TO COMPILE` as well as `MUST FAIL TO VERIFY`, and either kind may pin the
expected diagnostic with `EXPECT-ERROR`. Both directions were tested by breaking
`double_open.rs` two ways.

### Lease lock: many writers, repeated writes, a real server

Four changes, all verified (125, 0 errors):

- The server waits on every writer at once through a new `Inbox` in `proc.rs`,
  which wraps `recv_any`. Previously it round-robined with a blocking receive,
  so one silent writer stopped it serving anyone.
- Writers hold a lease across arbitrarily many writes, numbering them with the
  sequence field the protocol always had and never used (every write was
  sequence 0). The grant witness is stored in the service so each write can
  present it.
- The server refuses rather than reusing a token. `Msg::Denied` was added, and
  when the counter cannot advance the server denies from then on. The previous
  code saturated the counter, which would have handed two writers the same
  lease.
- The server tracks lease expiry against a real clock and refuses while a lease
  is live, and `serve_one` proves it REFINES a server that grants or refuses
  freely. `clock_now` has no `ensures`, so the refinement holds for any clock.

Not covered: writers arriving at run time. Each writer has its own FIFO channel
with the server, but the channels are created by the deployment, because an
endpoint cannot travel over a channel. Accepting connections would need endpoint
passing, which the model does not have.

### The lock server as a refinement stack

`serve_one`'s obligation is now stated at the lower layer, and `layer.rs` does
the rest. `LockHi` grants some higher lease number or refuses, and mentions no
clock; `LockLo` issues exactly one more than the last and carries the lease
bookkeeping; `LockRef` maps the implementation state by projection, discarding
`held` and `held_until`. `server_step_lifts` and `serve_one_is_abstract` carry a
concrete step up.

Two abstractions, not one: the clock and holder disappear, and "issues the next
number" relaxes to "issues something higher".

Checked by breaking it four ways: a constant refinement mapping fails 3.1(2);
reissuing the same number fails the implementation's own step relation; offering
an abstract grant where the implementation would fail breaks 3.1(1). Weakening
the abstract specification is NOT caught, and cannot be -- refinement constrains
the implementation only.

### All examples are services

The remaining seven are ported; nothing in `src/examples/` threads tokens
through arguments any more. 140 verified, 0 errors; four counterexamples
rejected; `verus --compile` still emits a running binary; nine behavioural
axioms.

  lossy            Transmitter, Sink
  heartbeat        Monitor, Watcher
  collector        Producer, Consumer (Consumer uses `Inbox`)
  twophase_fanout  Participant, Coordinator (Vec<Out>/Vec<In>, no MapTokens)
  twophase         TpcCoordinator, over the new `Out::call`
  chang_roberts    Node
  compose          BothLinks -- one service, two unrelated protocols
  multithread      spawns Participant services directly
  system           deploy builds services and hands each its endpoints

Two additions to `proc.rs` fell out of the port:

- `Inbox`, wrapping `recv_any`, for a service waiting on many peers.
- `Out::call`, the remote call over a reply channel opened for the purpose.
  `twophase` is now written against it, so the RPC no longer appears as a raw
  primitive in protocol code.

`In` also gained `rhist()` and now exposes the delivered index, which
`heartbeat`'s two-receives-are-distinct argument needs.

Three services grew a guard they did not have before, because the port made the
exhaustion case visible: `Monitor` stops beating when sequence numbers run out,
`BothLinks` likewise, and the lock server already refused. In each case
repeating a number would violate the protocol's own gate.

Still open: `movers.tex` describes the pre-service shape throughout and needs a
pass; `layers_demo.rs` is pure specification and was left alone.

---

# Plan for the four weaknesses found in design review

A review in August 2026 confirmed one soundness hole (endpoint relabelling, now
closed and covered by `counterexamples/relabel_endpoint.rs`) and four things
that do not work well. Two of them were not in this plan at all. Ordered by
value over cost, not by depth.

## A. Nothing runs a verified service end to end — **small**

`deploy` and `run` are never called, and `demo()` in `main.rs` reaches past the
endpoint API to a raw `mpsc` channel, by its own comment. So "the verified
source is the running program" is established for the toolchain and unexercised
for the design — which is the weakest kind of claim: true, and not evidence of
what it appears to be evidence of.

**Do:** replace `demo()` with a real deployment. Boot a `PingPong` instance,
`open_channel` both channels, build `Responder` and `Initiator`, spawn the
responder, run the initiator for a few rounds, print the answer. Then do the
same for the lease lock, which exercises `Inbox`, provenance and three services.

**Exit:** `verus --compile` produces a binary that runs a verified service and
prints a result that came through the endpoint API.

**Risk:** low. The one thing to watch is that `deploy` currently ends by
dropping the participants' tokens; a demo that wants to shut down cleanly may
need the services handed back, as `multithread.rs` does.

## B. `history_inv` is write-only — **contained, and validated**

A pairwise guarantee can be stated and proved as a machine invariant, but
`NetSM` exposes only `learn`, `learn_cause` and `witness_agree`. There is no way
for a service to consume `history_inv`. Heartbeat's "sequence numbers increase" is
proved and unusable from code — the one protocol whose guarantee needed `history_inv`
cannot act on it.

Note what is NOT the problem: a service that OWNS a channel reads its ordering
straight off `hist()`, which is how the lease lock's storage node works. The gap
is consuming a pairwise guarantee about a channel you do not own.

**Design**, mirroring `cause_gives`. Two witnesses in, a pure fact out:

    spec fn pair_gives(c: ChanId, m1: M, m2: M) -> bool;

    proof fn lemma_pair_gives(sent, c, i, j, m1, m2)
        requires history_inv(sent), i < j < sent[c].len(),
                 sent[c][i] == m1, sent[c][j] == m2,
        ensures  pair_gives(c, m1, m2);

    property!{ learn_pair(c, i, j, m1, m2) {
        have was_sent >= set { (c, i, m1) };
        have was_sent >= set { (c, j, m2) };
        require(i < j);
        birds_eye let s = pre.sent;
        assert(Inv::pair_gives(c, m1, m2)) by { Inv::lemma_pair_gives(..); };
    } }

`pair_gives` must be pure in `(c, m1, m2)` for the same reason `cause_gives`
must be pure: anything mentioning the histories is projected away when the
`birds_eye` binding goes out of scope.

Reading `sent` under `birds_eye` is sound here even though `sent` is not
monotone, because the CONCLUSION is a pure predicate about two messages. A pure
fact cannot later become false. Retaining anything about `s` itself would be
unsound, and the type system is what stops that.

**Validated:** `spike/pair_read.rs`, 9 verified, 0 errors. A watcher holding two
witnesses for a channel it does not own concludes `m1 < m2`. Deleting the
`learn_pair` call makes it fail, so it is not vacuous.

**Do:** move it into `tok.rs`; `heartbeat.rs`'s `Watcher` uses it to prove the
beats it received increase; the other seven protocols get `pair_gives` as
`true` and an empty lemma. Add a counterexample: a `Watcher` claiming
`m1 < m2` without the call.

**Cost:** one line in seven protocols, plus real definitions in `heartbeat`.

## C. `rpc` verifies a program that would not run — **partly blocked on D**

`absorb_handler` consumes the reply channel's send token at the call site, so no
participant can ever send the reply and `recv_abs` would block on a real queue
forever. Consistently, `twophase.rs` has NO participant service — only
`TpcCoordinator`. Model-sound, runtime-stuck.

This is a faithful rendering of Civl's `async call {:sync}` and would be fine in
Civl, where the handler still runs and the proof merely reorders it. Here the
token surgery makes the handler's send impossible rather than reordered. Fixing
that properly means the atomicity must come from the mover argument instead —
which is exactly what does not yet exist (D). So:

**Do now, honestly:**

1. Give `twophase.rs` a real `TpcParticipant` service that receives `Prepare`
   and sends its vote, and a coordinator path that uses plain send/recv — two
   interference points, no atomicity claim. That protocol then runs.
2. Mark `rpc`, `absorb_handler` and `recv_abs` explicitly as proof-level: they
   justify treating a call as atomic and are not a runnable calling convention.
   Say so in `tok.rs`, `README.md` and `movers.tex`, and exclude them from the
   "source that runs" claim.

**Do after D:** re-encode the handler so it holds its own reply capability and
really sends, with atomicity coming from the reduction argument rather than from
consuming a token. Only then can `rpc` be both atomic and runnable.

## D. Reduction is doing no work, and `wf` is not a checked yield invariant — **the real one**

No obligation anywhere depends on a block being atomic. `interference_point()`
is empty, mover types appear only in comments, and no activity's contract states
`R*.N.L*`. The proofs are sound WITHOUT reduction, because ownership makes every
fact a service uses stable. That is the development's actual result, and it is a
good one — but it means Civl's central ingredient is presently framing.

Two consequences, and they have the same fix.

**`wf` is described as a yield invariant but holds only at activity entry and
exit.** `Writer::write_once` contains two blocking receives and nothing requires
`wf` between them. Sound today only because of the ownership rule — which
nothing checks, and which the planned `pstate`/`pfacts` work could break
silently by introducing a field that is neither owned nor monotone.

**Phase 3 remains open**: nothing states that a body performs one step of a
declared action.

**Proposal: make the shape structural rather than documented.** Move blocking
out of activities and into the driver:

    pub trait Handler {
        type Req;
        spec fn wf(&self) -> bool;
        /// Receives NOTHING. The driver has already done the one blocking
        /// receive, so this body is `N . L*` by construction.
        fn handle(&mut self, from: usize, req: Self::Req)
            requires old(self).wf() ensures final(self).wf();
    }

The driver owns the `Inbox`, performs the single receive, and calls `handle`.
Then `R.N.L*` is a property of the type, not of a comment; `wf` is a genuine
yield invariant, because the only interference point is between `handle` calls;
and "this body is one abstract action" becomes stateable as a postcondition over
the service's own state and the histories it owns — which is exactly what
`LockServer::serve_one` already does by hand. Phase 3's second approach
(expressing the step over the tokens the thread holds) is this, made regular.

Services that INITIATE do not fit "handle a request" and are the thing to
resolve first. A writer is still a state machine — waiting for a grant, then
writing — so it needs an outbound `start`/`tick` alongside `handle`, and getting
that shape right is the design question. `Writer::write_once` is the test case:
two receives today, and it must become two handler states.

**Order:** spike the `Handler` shape on `pingpong` (trivial) and `leaselock`'s
writer (the hard case) before touching anything else. If the writer cannot be
expressed without contortion, the shape is wrong and the fallback is to keep
`Process` and instead state the ownership/monotonicity rule as an explicit,
reviewed side condition on every machine field — weaker, but honest.

**Exit:** every activity has exactly one interference point, at a place the type
system knows about; `wf` is required and re-established there; and one protocol
carries a postcondition tying a handler body to a declared abstract action.

## Dependencies

    A ---- independent, do first
    B ---- independent, spiked
    C.1 -- independent
    C.2 -- independent
    D ---- then C.3 (re-encode rpc) becomes possible

---

## Progress on the four weaknesses

**A — end to end: DONE.** `src/examples/lease_system.rs` boots a lease lock,
opens its five channels, builds the lock server, the storage node and a writer,
runs them on three threads and returns whether the last write was accepted.
`demo()` prints the result; everything below the print is verified code going
through the endpoint API.

    lease lock ran to completion; last write accepted = true

Chosen because the lease lock is the only protocol with no uninterpreted
parameters, so a deployment needs no configuration axiom. The others would each
need one to pin `vote`, `ok` or `good` — legitimate deployment facts, but
axioms, and worth avoiding for the demonstration that matters.

One writer, and straight-line rather than looped. Two reasons, both recorded
above: the storage node blocks on one writer's channel at a time instead of
waiting on all of them, and a terminating demo must choose matching step counts.
`system.rs` already shows the looped arbitrary-size deployment.

**B — `history_inv` consumable: DONE.** `NetInv` gained `pair_gives` and
`lemma_pair_gives`; `NetSM` gained the `learn_pair` property. Seven protocols
have the trivial version; `heartbeat` has the real one, and `Watcher::two_increase`
now proves the two beats it received increase — which before was not statable,
because `history_inv` was proved and unreachable from code.

Checked both ways: deleting the `learn_pair` call fails, and weakening
`pair_gives` to `true` fails.

**C — `rpc` proof-level: RESOLVED, and the plan above was wrong about it.**

The plan proposed giving `twophase.rs` a real participant. That cannot work, and
the reason is more interesting than the fix. Its reply channels are
`dyn_chan(1, j, k)`, minted by the COORDINATOR at call time, so a participant
would need the send endpoint of a channel somebody else created — and an
endpoint cannot travel over a channel. `twophase.rs` is proof-level
structurally, not incidentally.

So: `rpc`, `absorb_handler`, `recv_abs` and `twophase.rs` are now marked
proof-level in the source and excluded from the "runs" claim in `README.md`.
`twophase_fanout.rs` is the runnable two-phase commit.

This identifies ONE missing capability behind three separate limitations:
**endpoints cannot be sent over channels.** It blocks a runnable RPC,
participants that arrive at run time, and any accept-a-connection pattern.
Whether that is worth adding — and it would be a new trusted primitive plus a
message type that can carry an endpoint — is a design question this plan does
not answer.

**D — reduction: NOT STARTED.** Spike first, as written above: the `Handler`
shape on `pingpong`, then on `leaselock`'s writer, which is the case that
decides whether the shape survives contact.

**D — reduction: SPIKED, viable, with one design correction.**

`spike/handler.rs` (53 verified) and `spike/handler_writer.rs` (60 verified).

The shape holds. A service never receives; a driver owns the mailbox, does the
one blocking receive, and calls the handler:

    while i < rounds
        invariant h.wf(), inp.wf(),
    {
        h.tick();                 // N . L*  -- outbound half
        let m = inp.recv();       // the ONE interference point
        h.handle(m);              // N . L*  -- inbound half
    }

`wf` is required before the receive and re-established after the handler, so it
holds at the only point where another thread can interleave — a yield invariant
rather than a description of one — and `R . N . L*` is a property of the types.

Services that INITIATE need the outbound half, `tick`, and an explicit phase
field. That is what "the writer is a state machine" means concretely: the state
that used to live between two blocking receives inside one activity becomes a
field. `Writer2` in the spike has `WPhase { Idle, AwaitingGrant, Holding,
AwaitingAck }` and its two receives become two handler cases. The lease witness
was already stored in the service, so provenance survives the change unaltered.

**The correction the spike forced.** A handler cannot re-derive which channel a
message came from: the fact is ghost, so it cannot branch on it, and it does not
own the mailbox, so it cannot look. The driver must pass it in, which means the
trait carries

    spec fn iid(&self) -> InstanceId;
    spec fn chan(&self, k: int) -> ChanId;

and `handle`'s precondition relates the witness to `chan(from)` and supplies
`wit_inv` for it. The `Inbox` already knows all of this. Without it the writer's
`handle` would have to test at run time that its witness came from the grant
channel — not executable, and the wrong shape anyway, since the fact is static.

Remaining before this can be adopted:

1. `Inbox` needs `recv_any_wit`, returning the witness alongside the slot.
2. The driver has to establish `w.element().0 == h.chan(from)` from the
   `Inbox`'s own invariant, which means relating the service's `chan` to the
   mailbox's `rxs`. Straightforward, and the place a mismatch would be caught.
3. Port examples opportunistically. `Process` is NOT retired -- see below.
4. Then state, on one handler, a postcondition tying its body to a declared
   abstract action — closing Phase 3. `LockServer::serve_one` already does this
   by hand and becomes the template.

The fallback if step 2 or 3 goes badly is unchanged: keep `Process` and state
the ownership/monotonicity rule as an explicit reviewed side condition on every
machine field. Weaker, but honest.


### `Process` is not retired

The step above originally said "retiring `Process`". That was wrong, and
`spike/driver.rs` (60 verified) shows why: a handler bundled with its mailbox
IS a `Process`.

    pub struct Driven<M, Inv, H: NetHandler<M, Inv>> { pub h: H, pub inbox: Inbox<M, Inv> }

    impl<...> Process for Driven<M, Inv, H> {
        open spec fn wf(&self) -> bool { self.inv() }
        fn step(&mut self) {
            self.h.tick();                                       // N . L*
            let (k, m, Tracked(w)) = self.inbox.recv_any_wit();  // the ONE interference point
            self.h.handle(k, m, Tracked(w));                     // N . L*
        }
    }

So the two traits are layered, not rival. `NetHandler` is what a protocol author
writes; `Process` stays as the driver-facing interface and `run` is unchanged.
Porting a protocol is opt-in, one at a time, with no migration — and a service
with a genuine reason to block in an unusual shape can still be a plain
`Process`. The cost of that is honest and worth stating: the `R . N . L*`
guarantee then holds of the services that are handlers, not of the development
as a whole, so any claim about it has to name which.

`Driven::inv` is the one place the two halves are related — mailbox slot `k` is
the channel the handler says it is. That is where a mismatch is caught, and it
is the right place for it.

Two further corrections the spike forced, both about facts not chaining across a
call:

- `tick` and `handle` must preserve `iid()` and `chans()`. Otherwise the driver
  cannot relate the witness it was handed to the slot it came from, because
  `chans` is a function of a service that just changed.
- The channel map must be ONE value (`spec fn chans(&self) -> Seq<ChanId>`), not
  a quantified relation (`spec fn chan(&self, k: int) -> ChanId`). A `forall`
  recorded before a call is about a receiver that afterwards has no name; a
  single equality chains. In the driver, capture both sides as ghost data before
  anything moves, and the relation between two immutable values survives.

---

## Landed: handlers, and the RPC question answered

`NetHandler` and `Driven` are in `src/proc.rs`. `pingpong.rs` and
`leaselock.rs`'s `Writer` are ported; the lease-lock deployment drives the
writer through `Driven` and still runs. 158 verified, 0 errors.

`(R . N . L*)*` is handled correctly, and correctly means: each turn is one
atomic block, and repeating them is a sequence of blocks with `wf` checked
between. `run_rounds` in `pingpong.rs` states exactly that and no more.

Two mismatches are caught by `Driven::inv`, both tested: putting the mailbox
slots in the wrong order, and a handler declaring the wrong `chans()`.

### The RPC "hack" is not needed

The question was whether we could use the atomicity argument in the proof and a
real calling convention in the running code. The answer is that there is nothing
to hack around: **a blocking send-then-receive is already sound here.**

Claiming it is atomic in Civl's sense would be false — the caller genuinely
yields, and `L . R` does not reduce. But no proof in this development uses
atomicity. Every fact a service relies on is either in a token nobody else can
hold or in `was_sent`, which only grows, so nothing it knows can be falsified
while it waits. `pingpong.rs` demonstrates this directly: `waiting ==>
req.hist().len() > 0` is established before the request and still available
after the reply.

So the fallback that was offered — send, yield check, receive — is not a
fallback. It is the design, and under `NetHandler` it is the shape you get
automatically: `tick` sends, the driver's receive is the yield with `wf` checked
across it, `handle` reacts.

This also settles what `rpc` / `absorb_handler` / `recv_abs` are for: nothing we
need. They buy Civl's global atomicity, which no proof here uses, at the price
of being unrunnable. They stay marked proof-level; `twophase.rs` stays with
them as the demonstration of the technique.

### Still open

- Port the remaining seven examples to `NetHandler`, opportunistically.
- Phase 3: state, on one handler, a postcondition tying its body to a declared
  abstract action. `LockServer::serve_one` is the template, and the handler
  shape is what makes it regular rather than bespoke.

---

# A ladder of protocols towards Paxos

The goal is single-decree Paxos written against these abstractions, with the
rough edges it exposes treated as the point rather than as an inconvenience.
Going straight there would conflate several unknowns, so this is a ladder: each
rung is a small protocol that stresses exactly one thing Paxos needs, and each
is expected to produce one concrete framework change.

## What Paxos needs, and what is already there

Already available, and not the interesting part:

- Per-acceptor channels, so an acceptor owns its own histories.
- Ballots as `(round, proposer)`, so distinctness is structural and no global
  monotonicity of ballot numbers is needed. This is why protocol state in the
  machine is NOT on the critical path to Paxos.
- Set-valued provenance: `caused_by` already takes a set of causes, so a message
  justified by a quorum is expressible.

Not available. Each of these is a rung below.

- **Quorum gathering.** Collecting replies in arrival order while accumulating
  the set of who has replied, and building a `SetToken` from the witnesses.
- **Quorum intersection.** Two majorities of a finite set share a member.
- **A cross-participant invariant preserved at a caused send.** This is the one
  that will hurt; see the gap below.

## Confirmed gaps

**G1 — `lemma_history_inv_preserved` cannot see the provenance.** Its signature is

    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<M>>, c: ChanId, s: Seq<M>, m: M)
        requires Self::history_inv(sent), Self::gate(c, s, m), ...

so preserving a system-wide invariant at a send may use only the gate, which
reads one channel. Paxos's safety invariant relates messages on many acceptors'
channels, and the reason a proposer may send `Accept(b, v)` is precisely the
quorum of promises it holds witnesses for. Those witnesses are not available
here. The fix is to pass the causes and their guarantees into this lemma, which
means splitting it or widening it. Predicted to bite at rung 3.

**G2 — the finite-set lemmas for quorums are not in vstd.** `lemma_len_union`
and `lemma_len_intersect` are inequalities; the disjoint-union *equality* that
intersection needs is absent. `spike/quorum.rs` proves it by induction and then
derives quorum intersection: 3 verified, 0 errors. Roughly 30 lines, and it
should move into the library.

**G3 — `Inbox` does not carry its channel names.** `FanOut`/`FanIn` do, which is
what removed the per-slot quantifier friction. Every quorum protocol will hit
the same friction on the receive side. Small and mechanical.

**G4 — building a `SetToken` inside a loop is untested.** `SetToken::empty` and
`insert` exist, but accumulating one while relating it to a growing ghost set of
acceptors has never been done here.

## The rungs

**0. `Inbox` gets `ids`.** Enabling, small, uniform with `FanOut`/`FanIn`.

**1. Quorum acknowledgement.** Broadcast to n, proceed when a majority acks.
No safety property beyond "a majority really acked, and each ack is vouched
for". Stresses G3 and G4 and produces a `Quorum` helper: the accumulated
witnesses plus the ghost set of who they came from.

**2. Reliable broadcast.** Deliver a message only when a quorum has echoed it.
First real use of set-valued `caused_by` and `send_general`: the delivery is
justified by the quorum of echoes. Stresses `cause_gives` when the cause is a
set rather than one message.

**3. Quorum-replicated fencing register.** The lease lock's storage node,
replicated across n nodes, with a write accepted when a majority accepts it.
First use of quorum intersection: two writers each hold a majority, so some node
saw both, which orders them. First cross-participant safety argument, and the
rung where G1 is expected to bite.

**4. Synod without phase 1, then with it.** A proposer picks a ballot and sends
`Accept` to all; a value is chosen when a majority accepts. With one proposer
this is trivially safe. With two it is not, and the failure is the reason phase
1 exists. Writing the invariant, watching it fail, then adding phase 1 is the
cheapest way to get the invariant right before the full protocol.

**5. Single-decree Paxos.** Then, if it goes well, multi-decree.

## Deliberately not on this path

**Chandy--Lamport** needs happens-before across channels, which is a different
axis from quorums and would not help Paxos. It remains the better pilot for the
protocol-state-in-the-machine work, and the two tracks are independent.

**Phase 3** (tying a body to a declared abstract action) is not needed for
Paxos's safety proof, only for refining it to a Leslie or TLA specification.
Worth doing, but it does not block any rung here.

**Inductive sequentialization** was recorded as required for quorum gathering.
On reflection it is not, for the concrete proof: gathering in arrival order with
a loop invariant over a growing set of repliers is an ordinary loop invariant.
It would be needed to state the gathering as ONE abstract action, which is a
Phase 3 concern. Rung 1 will settle whether that reading is right.
