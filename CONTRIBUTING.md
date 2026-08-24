# Contributing

## The one rule

**Never trust a green run on its own.** A specification can verify because it is
unsatisfiable, vacuous, or about the wrong thing. After proving something, break
it and confirm it fails — and check *which* error you get.

This is not a style preference. Several claims in this repository verified and
meant nothing the first time, and were only caught this way. The counterexample
suite itself once went green while testing nothing, because the files had
stopped compiling and a compile error exits non-zero just like a verification
error.

`docs/proving.md` is the working guide: the framework's abstractions, the traps,
and the rules that cost real time to find. Read it before writing proofs. It is
more useful than the write-up for anyone actually changing code.

## Before opening a pull request

```
./verify.sh --run
```

must pass. It checks three things, and all three matter:

- the development verifies, with no `assume` and no `admit`;
- every counterexample is rejected, **and in the declared way**;
- the demo compiles and runs, so the verified source is still the running source.

CI runs the same script on a pinned Verus version. Nothing else is checked, and
nothing else needs to be.

## Workflow

Feature branch, then a pull request to `main`. `main` stays green.

Proof diffs are easy to get subtly wrong in ways that still verify — a weakened
gate, a vacuous postcondition, a quantifier that no longer says what it did — so
the reviewable diff is the point, not a formality.

## Adding a counterexample

Every file in `counterexamples/` must be rejected, and declares how:

```
// MUST FAIL TO VERIFY     -- must reach verification with errors
// MUST FAIL TO COMPILE    -- must not compile; ownership enforces it
// EXPECT-ERROR: <regex>   -- and must fail with THIS diagnostic
```

`EXPECT-ERROR` is what makes the suite worth having. Without it, a file that
fails for an unrelated reason — a typo — counts as a pass.

Break each new counterexample two ways before committing it: make it succeed,
and make it fail differently. Both must be reported as failures by
`counterexamples/check.sh`.

Prefer a property that ownership enforces over one the solver checks. Opening a
channel twice is a `MUST FAIL TO COMPILE`, because `make_endpoints` consumes the
channel's tokens and the second call is a use-after-move. That costs no
assumption, no invariant and no solver time, and it cannot be defeated by a weak
specification.

## Adding a protocol

1. Declare the message type and the protocol's parameters (`uninterp spec fn`).
2. Implement `NetInv` from `src/tok.rs`.
3. Write each participant as a struct owning its `Out`/`In` endpoints, with its
   activities as ordinary methods. Prefer `NetHandler` (`src/proc.rs`) to
   `Process`: a handler never blocks, so the driver owns the one interference
   point and the invariant is checked across it.
4. Wire it into a deployment. A component verified under preconditions nobody
   discharges proves very little — if two components' requirements were jointly
   unsatisfiable, each would still verify alone.

## Trusted surface

Nine `external_body` declarations, listed in `README.md`. Adding one is a design
decision, not an implementation detail: say in the pull request what is now
assumed and why it cannot be proved. Several assumptions that earlier versions
carried are now theorems, and that direction is the one to keep travelling.

`spike/` holds design experiments that verify but are deliberately not
integrated. Putting something there is a legitimate outcome — it records that a
thing was tried and what it cost.
