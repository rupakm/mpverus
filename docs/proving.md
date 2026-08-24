# Working on proofs in this repository

Notes for someone picking this up. Everything here was learned by hitting it,
and most of it cost more time than it should have.

## Orientation

    ./tools/verus-arm64-macos/verus src/main.rs --crate-type=bin      # ~2s
    ./tools/verus-arm64-macos/verus src/main.rs --crate-type=bin \
        --compile -o /tmp/civl && /tmp/civl                           # and it runs
    bash counterexamples/check.sh

Reading order:

1. `src/proc.rs` — the programming model, and the only thing a protocol author
   writes code against. Endpoints own their channel tokens, a service owns its
   endpoints, and `Process::wf` is the service's invariant.
2. `src/examples/pingpong.rs` — the smallest protocol.
3. `src/tok.rs` — `NetInv` (what a protocol declares), `NetSM` (the one network
   state machine every protocol shares), and the five trusted primitives.
4. `src/examples/leaselock.rs` — the largest: three services, provenance, and a
   refinement stack.
5. `docs/movers.pdf` for the ideas, `docs/plan.md` for what is open.

Current state: 196 verified, 0 errors, no `assume` or `admit`, nine behavioural
`external_body` declarations.

## Working method

**Never trust a green run on its own.** A specification can verify because it is
unsatisfiable, vacuous, or about the wrong thing. After proving something, break
it and confirm it fails — and check *which* error you get. Every substantive
claim in this repository has been checked this way, and several were vacuous the
first time.

**Check the reason for a failure, not just the fact.** The counterexample suite
once went green while testing nothing: the files had stopped *compiling* after a
refactor, and a compile error exits non-zero just like a verification error.
Files now declare how they must fail and may pin the diagnostic; see
"Some properties are types" below.

**Preconditions nobody discharges prove very little.** A service verified under
assumptions no caller establishes could have jointly unsatisfiable requirements
with its peers and still verify. `src/examples/system.rs` discharges them by
construction; if you add a service, wire it in.

**Before deleting something that looks unused, test the claim — and test it in
the right direction.** `Layered` and `lemma_send_gate_st` in `heartbeat.rs` are
called by almost nothing and look removable. They are a consistency condition:
`lemma_send_gate_st` proves `st_send ==> st_send_gate`, so it catches a layer
that CLAIMS a gate the machine does not enforce. Add a conjunct to
`st_send_gate` that the machine never checks and it stops verifying.

Weakening `st_send_gate` does not break it, and cannot: a weaker conclusion is
easier to prove. Under-claiming a gate is caught elsewhere, by whatever needed
the gate to be strong. I asserted the weakening direction here before testing
it, and it was wrong.

## Verus in this version

- `Set` is **finite**. `Set::new(pred)` returns `Option<Set>`; for an unbounded
  set use `ISet`.
- `Map::new(s: Set<K>, fv)` takes a **set**, not a predicate.
- There is no `!~=`. Write `!(a =~= b)`.
- In a postcondition on `&mut self`, write `final(self)` and `old(self)`; a bare
  `self` is rejected as ambiguous.
- Closures may carry `requires`/`ensures`:
  `|| -> (r: T) ensures r == 3 { 3 }`. `vstd::thread::spawn` passes the
  `ensures` through the `JoinHandle`.
- `&mut v[k]` on a `Vec` works, which is what makes a service with a vector of
  endpoints possible.
- Trait **default** spec-function bodies are not reliably visible at an impl. A
  protocol relying on the default `needs_cause` verified in one crate and failed
  in another. Override explicitly anywhere the default's *body* must be known.

## The programming model

A service is a struct holding its endpoints and its local state. Its activities
are ordinary methods; its invariant is `Process::wf`. Activity bodies carry no
ghost arguments at all — that is the point of the layer.

    pub struct Responder { pub req: In<Msg, PingPong>, pub rsp: Out<Msg, PingPong>, pub val: u64 }

    impl Process for Responder {
        open spec fn wf(&self) -> bool {
            &&& self.req.wf() && self.rsp.wf()
            &&& self.req.id() == ping_chan() && self.rsp.id() == pong_chan()
            &&& ok(self.val)
        }
        fn step(&mut self) {
            let _m = self.req.recv();
            self.rsp.send(Msg::Pong(self.val));
        }
    }

What the pieces are for:

- `Out<M, Inv>` — a sender plus the token for that channel's send history plus
  an instance handle. `id()`, `hist()`, `iid()`, `wf()`. Not duplicable, which
  is where "one sender per channel" comes from, and with it the fact that `send`
  is a left mover.
- `In<M, Inv>` — the dual over the consumption record. `recv()` returns the
  message with the protocol's guarantee; `recv_wit()` also returns the witness
  and exposes which index was delivered. `rhist()` is what has been consumed.
- `Inbox<M, Inv>` — several inbound channels waited on together, wrapping
  `recv_any`. Use it whenever a service serves many peers: with one `In` per
  peer the service must choose which to block on, and a silent peer stops it
  serving anyone.
- `Out::call` — a remote call over a reply channel opened for the purpose. Both
  halves are left movers, so the call contains no interference point and is
  atomic to its caller.
- `open_channel` / `open_new_channel` — the only ways to get endpoints. They
  consume the channel's tokens, which is what makes opening a channel possible
  exactly once.
- `Process` / `run` — `wf` plus `step`, and a driver loop.

**Use `recv` unless you need the witness.** `recv_wit` is for the case where the
message will later serve as provenance for something this service sends, or
where the delivered index matters.

**Do not name the inherent invariant `wf`.** A service with both an inherent
`wf` and `Process::wf` resolves ambiguously and the trait method silently
becomes self-referential — it verifies and means nothing. Call the inherent one
`inv` and let `Process::wf` delegate.

**Put exhaustion in the activity's precondition, not the invariant.** A monitor
whose sequence numbers can run out cannot maintain `seq < u64::MAX` as an
invariant. Require it on the activity, and have `step` guard the call:

    fn step(&mut self) { if self.seq < u64::MAX { self.beat_and_wait(); } }

Three services needed this. In each case repeating a number would violate the
protocol's own gate, so stopping is the only correct behaviour — and porting to
services is what made the case visible, since the old code took the counter as a
parameter and never confronted it.

**Do the bookkeeping before the activity.** In a round-robin `step`, advance the
cursor and then call the activity, so the activity's postcondition is the last
thing said about the service. The other order forces you to re-prove the whole
invariant after the assignment.

## Handlers: services that never block

`Process::step` may block anywhere inside itself, so `wf` is an invariant at
activity entry and exit only — a body with two blocking receives has an
interference point in the middle where nothing is required. `NetHandler` moves
the blocking into the driver:

    h.tick();                                        // N . L*  outbound
    let (k, m, Tracked(w)) = inbox.recv_any_wit();   // the ONE interference point
    h.handle(k, m, Tracked(w));                      // N . L*  inbound

so `R . N . L*` is a property of the type and `wf` is required across the only
point where another thread can interleave. Repeating it is `(R . N . L*)*` — a
SEQUENCE of atomic blocks with a checked invariant between them, not one block.
Nothing claims otherwise.

**`NetHandler` does not replace `Process`.** `Driven<M, Inv, H>` bundles a
handler with its mailbox and IS a `Process`, so `run` and every deployment are
unchanged and adopting the shape is per-service. The cost of that is worth
stating: the guarantee holds of the services that are handlers, not of the
development, so a claim about it has to name which.

Four rules, all learned by hitting them:

- **`tick` and `handle` must preserve `iid()` and `chans()`.** Otherwise the
  driver cannot relate the witness it was handed to the slot it came from,
  because `chans` is a function of a service that just changed.
- **The channel map is one value, not a quantified relation.** `spec fn
  chans(&self) -> Seq<ChanId>`, not `spec fn chan(&self, k: int)`. A `forall`
  recorded before a call is about a receiver that afterwards has no name; a
  single equality chains. Same rule as the vectors below — capture both sides
  as ghost DATA and the relation between two immutable values survives.
- **`handle` must bound `from`.** Without `0 <= from < chans().len()` the
  channel lookup is unspecified and the guarantee attached to it says nothing.
- **A handler cannot branch on which channel a message came from.** The fact is
  ghost, so it is not executable, and the handler does not own the mailbox, so
  it cannot look. The driver supplies it as a precondition. Trying the run-time
  check gives `cannot access spec-mode place in executable context`.

A service that INITIATES needs `tick` and an explicit phase field. That is what
"a client is a state machine" means concretely: state that used to live between
two blocking receives inside one activity becomes a field, and the two receives
become two handler cases. `leaselock`'s `Writer` is the worked example.

## RPC needs no atomicity argument here

A request-response exchange is `tick` sending and `handle` receiving, with the
interference point in between. It is two atomic blocks, not one, and that is
fine — nothing a service knows can be falsified while it waits, because its
facts are about tokens no one else can hold and about `was_sent`, which only
grows. `pingpong.rs` carries the demonstration: `waiting ==> req.hist().len() >
0` is established before the request and asserted after the reply.

So do NOT reach for `rpc` / `absorb_handler` / `recv_abs`. They buy atomicity in
Civl's global sense, which no proof here uses, and they pay for it by consuming
the reply channel's send token so that no handler can ever reply — see
`docs/plan.md` item C.

## Vectors of endpoints

Every service holding a `Vec` of endpoints hits the same wall. A per-index
invariant must be a predicate over the **vectors**:

    pub open spec fn tpcf_pair_ok(reqs: Seq<Out<..>>, rsps: Seq<In<..>>, j: int) -> bool

not a method on the service. As a method it mentions the whole receiver, so it
survives neither assigning an unrelated field nor a call that touches only one
of the vectors. `collector.rs` needed the same fix for `Inbox`: state it over
`self.hub.rxs@`, not over `self.hub.id(j)`.

After touching index `k`, re-establish the quantifier:

    let ghost v0 = self.reqs@;                    // at the top of the body
    ...
    assert forall|j: int| 0 <= j < len implies #[trigger] pair_ok(self.reqs@, w@, j) by {
        assert(pair_ok(v0, w@, j));               // it held before
        if j != k as int { assert(self.reqs@[j] == v0[j]); }
    }

When pushing, snapshot the pushed value first — `let ghost ro = req_out;` before
`push` — since after the move you cannot name it, and you will need to say
`reqs@[j] == ro`.

## Tokens and ownership

**You cannot move out of `tracked &mut`.** Verus would need a replacement value
it cannot fabricate. Take the token by value and return it, or take `&mut`
throughout and never move. This is why `recv` is not derived from `recv_any`.

**A `Instance` is duplicable.** `inst.clone()` gives full equality, so every
endpoint carries its own and nothing needs threading. There is no need for a
`&'static` instance.

**Spawned closures need an explicit `requires`.** Verus otherwise infers `true`
and requires the body to verify unconditionally. State what the thread needs
over the values moved in; the obligation is checked at the spawn site, which is
where the wiring is decided. Since a service *is* the unit of ownership, this is
usually just `requires p.wf()`.

**To mention a value after it is moved, snapshot it:** `let ghost iid = inst.id();`.

**`Tracked(x)` cannot be destructured in a match pattern.** Bind the whole value
and call `.get()` inside a `proof` block.

**A method returning something the caller must put back has to say so.** An
earlier `coordinator_fanout` borrowed two `MapToken`s and said nothing about
them in its postcondition, so a caller could not reinsert them. This is
invisible until something actually composes the components — which is what
`system.rs` is for.

## Loops

**Everything preserved across a loop must appear in the invariant, including
facts about values the loop only reads.** This is the rule that will cost you
the most time. A loop that merely clones `inst` still loses `inst.id() == iid`
unless the invariant says so.

With services this is usually `invariant self.inv(),` plus whatever the loop is
accumulating, and the body must re-establish `self.inv()` explicitly after
touching a vector.

**A loop that pops from a vector should decrease on the vector's length**, not
on a counter difference, which can underflow.

## Triggers and quantifiers

**Prefer fewer quantified variables.** A variable determined by another is
redundancy the solver pays for.

**A `forall` nested under a `forall` needs an explicit inner trigger,** and a
generic lemma taking the inner predicate as a `spec_fn` closure may still fail
to connect. When that happens, write the `assert forall ... by` inline.

**An empty `assert forall ... implies ... by { }` is usually a trigger prompt,
not dead code.** Deleting one can break the proof. But measure: two such blocks
in `twophase_fanout.rs` were genuinely redundant, and removing them cut that
function's solver cost by 4%. Test, do not guess.

**Tuple-typed `forall` inside a state machine invariant may fail to parse.**
Use separate variables.

**Verus will not guess an existential witness.** Name it, assert the body at
that witness, then assert the existential. This comes up at every `send_caused`
and in every refinement postcondition.

## Cross-channel facts, and why they need provenance

A gate is given one channel's history, so it cannot say anything about another
channel. "This token was really issued by the server" is that kind of statement,
and no amount of strengthening the gate on the write channel will express it.

`history_inv` looks like the escape hatch, since it ranges over the whole `sent` map.
It is not: `lemma_history_inv_preserved` must prove preservation from `gate(c, s, m)`
alone, so the gate's blindness propagates into it. The same wall, one level up.

The mechanism is provenance, four members of `NetInv`:

- `needs_cause(c, m)` marks the messages that must be justified. Sending one
  through plain `send` is rejected.
- `caused_by(c, m, causes)` says what counts, where `causes` is a set of
  `(channel, position, message)`. **Derive the expected channel from `c`**
  rather than quantifying over it, so a participant cannot present somebody
  else's message: `acq_rsp(c.ix[0])` ties the grant to the writer whose channel
  the write arrived on. A set, not one message, so a quorum can justify too.
- `cause_gives(c, m)` is what a reader learns. **This must mention only `c` and
  `m`.** The reader reaches the justification through an existential it cannot
  name, so anything said about the cause directly is projected away.
- `lemma_cause_gives` discharges it, and may assume `wit_inv` of the justifying
  message, because everything ever sent satisfies the protocol's guarantee.
  That is where the content comes from.

The sender presents a witness from `recv_wit`. For one cause use `send_caused`;
for several, build a `SetToken` and call `send_general`. The reader calls
`inst.learn_cause(..)`.

Two traps.

**The vacuous version.** If `cause_gives` follows from `c` and `m` alone, the
whole chain proves nothing and still verifies. Test by deleting the
`learn_cause` call: the proof must fail.

**Why reading the whole record is sound.** `learn_cause` uses `birds_eye` to
read `was_sent`, which no thread owns. Sound only because `was_sent` grows and
never shrinks, so a justification found this way cannot be removed by a later
step of any thread. The same reasoning would be wrong for `sent`.

## Layers and refinement

When a service's decision depends on something the proof should not rely on — a
clock, a heuristic, a cache — give the primitive that reads it **no `ensures`**.
An `external_body` function with no postcondition asserts nothing, so it costs
no assumption and every proof downstream holds for any behaviour of it.
`clock_now` in `leaselock.rs` is the case.

Declare the two layers as `Spec`s and the mapping as a `Refines`, and have the
activity's postcondition say only that it took a step of the **lower** layer:

    &&& h1 == h0.push(h1.last())
    &&& exists|a: LockAct| #[trigger] LockLo::step(
            a, Msg::Acquire, h1.last(), old(self).st(), final(self).st())

`lift` carries it up. Keeping the code's obligation at the lower layer is what
lets the layers be re-stated without touching any activity body. Give the
service an `st()` returning its transition-system state.

**Choose the concrete state so the mapping is as close to the identity as it can
be.** An earlier lock server stored "next token to issue" and mapped it to
"highest issued" by subtracting one; the off-by-one leaked into the abstract
gate, which had to read `hi < MAX - 1` for no reason a reader could see. Storing
"highest issued" made the mapping a projection and the two gates coincide.

**What refinement does and does not catch.** It constrains the implementation
only. Weakening the abstract specification is trivially refined and will not be
caught — the strength of the abstract layer is what downstream proofs rely on
and has to be reviewed on its own. Both directions of Civl 3.1 are live, though:
mapping the state to a constant fails 3.1(2), and offering an abstract action
where the implementation would fail breaks 3.1(1).

**Refinement lemmas may assume the concrete invariant.** Refinement is only
appealed to at reachable states, so `lemma_gate` and `lemma_step` carry
`Lo::inv`. Without it an abstraction that forgets information the gate needs is
unprovable.

**`abs_act` is a function of the action alone.** An action cannot be visible in
some states and invisible in others. State-dependent invisibility belongs on the
abstract side, where the transition admits the identity as a disjunct. `None` is
for actions that are always internal.

Capture `let ghost pre_x = self.x;` at the top of the activity — `old(self)` is
not available in the body — and assert the disjunct you took at the end of each
branch.

## Where to state a protocol-global invariant

Two hooks, and choosing the wrong one costs an order of magnitude.

**`history_inv`, over `sent`.** For a property of ONE channel's ORDER: an ordered
journal, increasing sequence numbers. It needs the sequence, so it has to live
here.

**`record_inv`, over `was_sent`.** For a property that says *some message exists
somewhere else* -- anything relating two channels. `was_sent` only grows, so
preservation concerns the ONE element just added. `sent` is a map of sequences
that changes structurally at every send, so the same property stated there means
reasoning about a map insertion and sequence indices every time.

Measured on one property, stated both ways in `spike/crosschan.rs`: **two lines
of inductive step against twenty-one.** Both verify, so this is a cost
difference rather than a capability one -- but at twenty-one lines per property
per protocol it decides whether a proof is written at all. The Paxos clause was
abandoned in the `sent` form and went through in the `was_sent` form.

Both preservation lemmas receive the witnesses the sender presented. That is
what makes a cross-channel property provable at all: a gate reads one history,
and the reason the send was legal is the cause.

One trap when writing the guard. Say "this channel is an X channel" **by
equality** -- `c == p2b(c.ix[0], c.ix[1])` -- not by picking the name apart
(`c.fam == 4 && c.ix.len() == 3`). The second does not pin every index, so
`wit_inv` cannot be instantiated at it, and the guarantee attached to the
channel is unavailable. This cost a round trip.

## Some properties are types, not proofs

Not every obligation is a verification condition. Opening one channel twice is
prevented because `make_endpoints` consumes the channel's two tokens and the
machine holds exactly one of each, so a second call is a use-after-move. There
is nothing to prove and nothing to get wrong.

Prefer this when it is available. It costs no assumption, no invariant and no
solver time, and it cannot be defeated by a weak specification.

The counterexample suite covers both kinds. A file declares how it must fail:

    // MUST FAIL TO VERIFY     -- must reach verification with errors
    // MUST FAIL TO COMPILE    -- must not compile; ownership enforces it
    // EXPECT-ERROR: <regex>   -- and must fail with THIS diagnostic

The `EXPECT-ERROR` line matters. Without it a file failing for an unrelated
reason — a typo — counts as a pass, which is how this suite once went green
while testing nothing. Break each counterexample two ways when adding it: make
it succeed, and make it fail differently.

## The network state machine

There is one, `NetSM<M, Inv>` in `src/tok.rs`, shared by every protocol and
parameterised by an implementation of `NetInv`. A protocol writes no state
machine. An earlier version generated one per protocol with a `macro_rules!`
wrapper around `tokenized_state_machine!`; that is gone, and with it three
hygiene workarounds.

**A `macro_rules!` cannot usefully wrap `tokenized_state_machine!`.** Three
independent reasons, all of which cost real time to find:

- `==>` is a two-token operator and expansion loses the jointness the parser
  needs, so generated text has to spell it `!a || b`. The symptom is "expected
  an expression" pointing into the macro definition.
- Verus syntax cannot be captured as `:block` or `:expr`, because `==>` is not
  Rust. Everything has to be a `tt` slurp.
- Hygiene severs `pre` and `post`, which come from the inner procedural macro.

**Type parameters need a `PhantomData` field.** A parameter used only in spec
positions is "never used" as far as the generated state struct is concerned.
`#[sharding(constant)] pub inv: PhantomData<Inv>` fixes it; this is the idiom
`vstd::rwlock` uses.

**A field type may be a protocol-supplied associated type** (`Map<int, Pr::P>`),
and `have f >= [k => v]` reads a `map` field without consuming it. Both were
checked in `spike/pstate.rs`, against the day protocol state moves into the
machine.

**Generic paths need qualifying.** `NetSM::State<M, Inv>::do_send(..)` does not
parse; write `<NetSM::State<M, Inv>>::do_send(..)`.

**A struct holding an external type needs `#[verifier::reject_recursive_types]`
on the parameter.** `Sender`/`Receiver` carry a real `mpsc` channel, so they do.

**Adding a field adds obligations everywhere.** Introducing the allocator meant
every transition had to re-establish `unallocated`; adding `history_inv` produced a
third lemma nobody anticipated. Expect one new obligation per transition per
invariant.

## Design rules specific to this framework

**The yield invariant is usually the gate remembered.** In six of the eight
protocols, `wit_inv(c, m)` is the same predicate as `gate(c, _, m)`, and
`lemma_gate_gives_inv` is empty. If you find yourself writing a different
predicate, check whether the gate is too weak.

The obligation is `gate(c, s, m) ==> wit_inv(c, m)`, so `wit_inv` may be weaker
than the gate but never stronger: a protocol may remember less than it enforced,
never more.

The two exceptions say what the rule is for. `heartbeat`'s guarantee is about
**pairs** of messages, and a witness names one message, so `wit_inv` is `true`
and the guarantee lives in `history_inv`. `leaselock`'s gate carries the journal
ordering, which is likewise about pairs. Note that `gate` may read the history
`s`, which is exactly what `wit_inv` cannot do — the structural reason the two
sometimes differ.

**Protocol constants are module-level `uninterp spec fn`s.** A protocol cannot
add fields to the machine, so a parameter such as "which channel is the link" is
a module-level function. `NetInv`'s members are static, so they can call it.

**Build channel names with `chan(fam, ix)`.** Distinctness is then structural
equality rather than an axiom. Requests are conventionally family 0, replies
family 1; two indices are reserved for channels created while the program runs.

**Distinguish who may send from the delivery discipline.** Who may send decides
whether a history can be exclusively owned, and therefore whether `send` is a
left mover; several senders require a family of channels. The delivery
discipline decides what a receiver may be handed and is receive-side only. An
unreliable link is the second kind and costs one line; unordered delivery from
many senders is the first kind and changes the model. Conflating them costs
either soundness or expressiveness — this was got wrong once and caught.

## Things that look wrong but are not

- `interference_point()` has an empty body and no specification. That is the
  point: nothing has to be re-established after an interference point, because a
  service's facts live in tokens no one else can hold. It is not trusted.
- `wit_inv` is `true` in `heartbeat.rs`. See above.
- Most of `NetInv`'s proof members are empty in most protocols. When the gate
  and the guarantee coincide and `history_inv` is `true`, every one of them is.
- `lossy.rs` does not implement `DetDelivery`. It cannot, and should not: an
  unreliable link may deliver any index at any time, so a remote call on such a
  link would be unsound. The trait bound is what prevents it.
- `make_endpoints` takes two tokens and gives them straight back. That is the
  point; see "Some properties are types".
- `Sender` and `Receiver` are `external_body` with private fields and an
  `uninterp spec fn id()`. This is a soundness requirement, not style: with the
  fields public, verified code could rebuild a handle around another channel's
  queue under a different name, and every precondition would still hold while
  the bytes went somewhere the model did not record. See
  `counterexamples/relabel_endpoint.rs`. Making the fields private alone does
  not work -- Verus then rejects field access inside `tok.rs` too -- so the type
  is opaque and the primitives that touch its fields are `external_body`.
- A writer that reuses its sequence number still verifies. Correct: it is simply
  refused from then on. The theorems here are about safety, never progress.

## Where the current gap is

**Reduction is currently doing no work.** No obligation anywhere depends on a
block being atomic: `interference_point()` is empty, mover types appear only in
comments, and no activity's contract states `R*.N.L*`. The proofs are sound
WITHOUT reduction, because ownership makes every fact a service uses stable --
it is in a token nobody else holds, or in `was_sent`, which only grows.
Reduction is needed only to say "this body is one abstract action", which is the
Phase 3 gap below. Read the mover vocabulary as an explanation of why the
ownership discipline is the right one, not as machinery that is running.

The latent rule this leaves is worth stating plainly, because nothing checks it:
**every fact a service relies on across an interference point must be owned or
monotone.** `wf` holds at activity entry and exit, not between the blocking
receives inside an activity; it is sound today only because of that rule. Adding
a machine field that is neither owned nor monotone would break it silently, and
the planned `pstate`/`pfacts` work is exactly where that could happen.

**`history_inv` is write-only.** A pairwise guarantee can be stated and proved as a
machine invariant, but `NetSM` exposes only `learn`, `learn_cause` and
`witness_agree`; there is no way for a service to consume `history_inv`. Heartbeat's
"sequence numbers increase" is proved and unusable from code. The missing piece
is a `birds_eye` property projecting `history_inv` to a pure predicate, mirroring
`cause_gives`.

**`rpc` verifies a program that would not run.** `absorb_handler` consumes the
reply channel's send token at the call site, so no participant can ever send the
reply and `recv_abs` would block on a real queue forever. Consistently,
`twophase.rs` has no participant service at all. This is a faithful rendering of
Civl's `{:sync}` and is model-sound, but it sits inside a repository that claims
the verified source is the running program, and that claim does not extend here.

**Nothing runs a verified service end to end.** `deploy` and `run` are never
called, and `demo()` reaches past the endpoint API to raw `mpsc` by its own
admission. "It compiles and runs" is established for the toolchain and
unexercised for the design.


No combinator ties a running function to a declared abstract action in general.
`leaselock.rs` does it by hand — `serve_one`'s postcondition names a step of
`LockLo`, and `server_step_lifts` carries it up — but that is a postcondition
written for one activity, not a general mechanism, and `Layered`/`BottomLayer`
derive a stack's bottom from the protocol without connecting it to any code.
`docs/plan.md`, Phase 3, has the candidate approaches.

Also open: protocol state that must be *related* to network state has to live in
one machine, and `NetSM`'s fields are fixed. That is what blocks global
monotonicity of the lock server's grants, mutual exclusion as opposed to write
serialization, and happens-before across channels. The design and its
feasibility spike are in `plan.md`.
