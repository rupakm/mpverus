// A lease lock with fencing tokens, as three kinds of process exchanging
// asynchronous messages.
//
//   the LOCK SERVER   hands out monotonically increasing lease tokens, one per
//                     acquire request. Its counter is an ordinary local
//                     variable; nothing about it is ghost state.
//   the STORAGE NODE  accepts a write only if its (token, sequence) strictly
//                     exceeds every write it has already accepted, and appends
//                     accepted writes to a journal. This is the fencing check.
//   the WRITERS       acquire a lease, then send writes. They are concurrent,
//                     and a writer is never told that its lease expired.
//
// Lease expiry is modelled by nondeterminism rather than by time: a writer may
// be granted a lease at any point, so an earlier writer's token can be
// superseded while it still believes it holds the lock, and its next write is
// then refused by the storage node. Nothing in the writer's code detects this,
// which is the situation the protocol is designed for.
//
// The property proved is WRITE SERIALIZATION, which is what a fencing token
// buys and is the top-level theorem of the corresponding Leslie model: the
// journal is strictly ordered by (token, sequence). It is deliberately NOT
// mutual exclusion -- two writers may believe simultaneously that they hold the
// lease, and the protocol still behaves.

use vstd::prelude::*;
use vstd::tokens::KeyValueToken;
use crate::tok::*;
use crate::proc::*;
use crate::layer::*;
use vstd::tokens::InstanceId;

verus! {

// ---------------------------------------------------------------------------
// Channels. One family per direction, indexed by writer where per-writer.
// ---------------------------------------------------------------------------
pub open spec fn acq_req(w: int) -> ChanId { chan(0, seq![w]) }   // writer  -> server
pub open spec fn acq_rsp(w: int) -> ChanId { chan(1, seq![w]) }   // server  -> writer
pub open spec fn wr_req(w: int)  -> ChanId { chan(2, seq![w]) }   // writer  -> storage
pub open spec fn wr_rsp(w: int)  -> ChanId { chan(3, seq![w]) }   // storage -> writer
pub open spec fn journal()       -> ChanId { chan(4, seq![]) }    // storage -> the record

#[derive(Structural, PartialEq, Eq)]
pub enum Msg {
    Acquire,
    Granted(u64),               // lease token
    Denied,                     // the server would not issue a lease
    Write(u64, u64, u64),       // token, sequence, value
    Accepted(u64, u64, u64),    // token, sequence, value
    Refused,
}

/// Writes are ordered lexicographically by (token, sequence).
pub open spec fn lex_lt(a: Msg, b: Msg) -> bool {
    a->Accepted_0 < b->Accepted_0
        || (a->Accepted_0 == b->Accepted_0 && a->Accepted_1 < b->Accepted_1)
}

/// A journal is serialized when it is strictly increasing in that order.
pub open spec fn serialized(h: Seq<Msg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len() ==> lex_lt(#[trigger] h[x], #[trigger] h[y])
}

pub struct Lease;

impl NetInv<Msg> for Lease {
    /// Two obligations, both local to the channel being written.
    ///
    /// The fencing check: the storage node may append to the journal only a
    /// write that strictly exceeds everything already there. This is what
    /// refuses a stale leader, and it is a gate rather than a blocking
    /// condition because a storage node that appended out of order would be
    /// wrong, not early.
    ///
    /// And well-formedness: each channel carries only the messages of its
    /// direction, so a receiver knows what it is looking at.
    open spec fn gate(c: ChanId, s: Seq<Msg>, m: Msg) -> bool {
        &&& (c == journal() ==> m is Accepted && m->Accepted_0 != 0
                && forall|x: int| 0 <= x < s.len() ==> lex_lt(#[trigger] s[x], m))
        &&& (forall|w: int| c == #[trigger] acq_rsp(w)
                ==> (m is Granted && m->Granted_0 != 0) || m is Denied)
        &&& (forall|w: int| c == #[trigger] wr_req(w)  ==> m is Write)
        &&& (forall|w: int| c == #[trigger] acq_req(w) ==> m is Acquire)
    }

    /// What a receiver may conclude from a message alone.
    open spec fn wit_inv(c: ChanId, m: Msg) -> bool {
        &&& (c == journal() ==> m is Accepted && m->Accepted_0 != 0)
        &&& (forall|w: int| c == #[trigger] acq_rsp(w)
                ==> (m is Granted && m->Granted_0 != 0) || m is Denied)
        &&& (forall|w: int| c == #[trigger] wr_req(w)  ==> m is Write)
        &&& (forall|w: int| c == #[trigger] acq_req(w) ==> m is Acquire)
    }

    open spec fn deliverable_at(v: Seq<Msg>, i: nat) -> bool { fifo_deliverable(v, i) }

    /// WRITE SERIALIZATION, as a system-wide invariant.
    open spec fn history_inv(sent: Map<ChanId, Seq<Msg>>) -> bool {
        sent.dom().contains(journal()) ==> serialized(sent[journal()])
    }

    /// A write must point at the grant that issued its token. The gate on
    /// `wr_req` cannot state this: it sees only that channel's history, and the
    /// grant was sent on another channel entirely.
    open spec fn needs_cause(c: ChanId, m: Msg) -> bool {
        c.fam == 2 && c.ix.len() == 1 && m is Write
    }

    /// The only acceptable justification is the matching grant on this
    /// writer's own reply channel. A writer cannot present another writer's
    /// grant, because `caused_by` fixes the channel from `c`.
    open spec fn caused_by(c: ChanId, m: Msg, causes: Set<(ChanId, nat, Msg)>) -> bool {
        exists|j: nat| causes.contains((acq_rsp(c.ix[0]), j, Msg::Granted(m->Write_0)))
    }

    /// The same, for one cause: the grant on this writer's own reply channel.
    open spec fn caused_by1(c: ChanId, m: Msg, d: ChanId, j: nat, m2: Msg) -> bool {
        d == acq_rsp(c.ix[0]) && m2 == Msg::Granted(m->Write_0)
    }

    proof fn lemma_caused_by1(c: ChanId, m: Msg, d: ChanId, j: nat, m2: Msg) {
        assert(set![(d, j, m2)].contains((acq_rsp(c.ix[0]), j, Msg::Granted(m->Write_0))));
    }


    /// What the storage node gets to conclude: the token in the request was
    /// issued by the server, and so is nonzero. The writer cannot manufacture
    /// this, because `send_caused` demands the witness.
    open spec fn cause_gives(c: ChanId, m: Msg) -> bool {
        Self::needs_cause(c, m) ==> m->Write_0 != 0
    }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn pair_gives(c: ChanId, m1: Msg, m2: Msg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<Msg>>, c: ChanId,
                                i: nat, j: nat, m1: Msg, m2: Msg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Msg>, m: Msg) { }

    proof fn lemma_cause_gives(c: ChanId, m: Msg, causes: Set<(ChanId, nat, Msg)>) {
        // The justification is a grant on this writer's own reply channel, and
        // everything ever sent there carries a nonzero token.
        let j = choose|j: nat|
            causes.contains((acq_rsp(c.ix[0]), j, Msg::Granted(m->Write_0)));
        assert(causes.contains((acq_rsp(c.ix[0]), j, Msg::Granted(m->Write_0))));
    }

    // No cross-channel property to state over the record.
    open spec fn record_inv(was_sent: Set<(ChanId, nat, Msg)>) -> bool { true }
    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, Msg)>,
                                     sent: Map<ChanId, Seq<Msg>>,
                                     c: ChanId, s: Seq<Msg>, m: Msg,
                                     causes: Set<(ChanId, nat, Msg)>) { }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) {
        let s0 = Map::new(chans, |c: ChanId| Seq::<Msg>::empty());
        if s0.dom().contains(journal()) { assert(s0[journal()].len() == 0); }
    }

    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<Msg>>, c: ChanId) {
        let post = sent.insert(c, Seq::<Msg>::empty());
        if post.dom().contains(journal()) {
            assert forall|x: int, y: int| 0 <= x < y < post[journal()].len()
                implies lex_lt(#[trigger] post[journal()][x], #[trigger] post[journal()][y]) by {
                if c == journal() { assert(post[journal()].len() == 0); }
            }
        }
    }

    /// The gate is exactly what makes this go through: the new entry exceeds
    /// every existing one, and the existing ones were already ordered.
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<Msg>>,
                                   was_sent: Set<(ChanId, nat, Msg)>,
                                   c: ChanId, s: Seq<Msg>, m: Msg,
                                   causes: Set<(ChanId, nat, Msg)>) {
        let post = sent.insert(c, s.push(m));
        if post.dom().contains(journal()) {
            assert forall|x: int, y: int| 0 <= x < y < post[journal()].len()
                implies lex_lt(#[trigger] post[journal()][x], #[trigger] post[journal()][y]) by {
                if c == journal() {
                    assert(post[journal()] == s.push(m));
                    if y < s.len() { assert(lex_lt(s[x], s[y])); }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The three services.
//
// Each owns its endpoints and its local state, and its `wf` is its invariant.
// Nothing in these bodies mentions a token or the state machine.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The lock server.
// ---------------------------------------------------------------------------

/// How long a lease lasts, in whatever unit the clock reports.
pub const LEASE: u64 = 1000;

/// Read the wall clock.
///
/// Unverified AND UNCONSTRAINED: it promises nothing about the value returned.
/// Every proof below therefore holds for any clock whatever -- one that jumps,
/// runs backwards, or stops. That is deliberate. Safety here must not depend on
/// clock behaviour, and giving this an `ensures` would quietly make it do so.
/// It adds no assumption for the same reason: it asserts nothing.
#[verifier::external_body]
pub fn clock_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

// ---------------------------------------------------------------------------
// The lock server as two layers.
//
// The implementation reads a clock and tracks an outstanding lease. None of
// that is visible from above: the abstract server simply decides, for reasons
// of its own, either to grant a lease numbered higher than any it has issued,
// or to refuse.
//
// The refinement forgets two things. It forgets the lease bookkeeping and the
// clock entirely, and it relaxes "issues exactly one more than the last" to
// "issues something higher". Anything proved against the abstract server
// therefore holds for any implementation making the same choice, however it
// makes it.
// ---------------------------------------------------------------------------

/// The two things a lock server can do.
pub enum LockAct { Grant, Refuse }

/// The implementation's state: the highest lease it has issued, plus the lease
/// bookkeeping the abstraction discards.
pub struct SrvState {
    pub hi: u64,
    pub held: bool,
    pub held_until: u64,
}

/// The ABSTRACT server. Its state is just the highest lease issued so far, and
/// it chooses between its two actions freely -- nothing here mentions a clock,
/// a lease duration, or a holder.
pub struct LockHi;

impl Spec for LockHi {
    type S = u64;
    type A = LockAct;
    type M = Msg;

    open spec fn inv(s: u64) -> bool { true }

    /// Granting must not fail while a higher lease number still exists.
    /// Refusing never fails.
    open spec fn gate(a: LockAct, req: Msg, s: u64) -> bool {
        match a { LockAct::Grant => s < u64::MAX, LockAct::Refuse => true }
    }

    /// Grant SOME higher number. This is the nondeterminism: the specification
    /// does not say which.
    open spec fn step(a: LockAct, req: Msg, resp: Msg, s0: u64, s1: u64) -> bool {
        match a {
            LockAct::Grant  => resp is Granted && resp->Granted_0 > s0
                                 && s1 == resp->Granted_0,
            LockAct::Refuse => resp is Denied && s1 == s0,
        }
    }
}

/// The IMPLEMENTATION, as a transition system. It issues exactly one more than
/// the last lease it issued, and carries lease state the layer above ignores.
pub struct LockLo;

impl Spec for LockLo {
    type S = SrvState;
    type A = LockAct;
    type M = Msg;

    open spec fn inv(s: SrvState) -> bool { true }

    open spec fn gate(a: LockAct, req: Msg, s: SrvState) -> bool {
        match a { LockAct::Grant => s.hi < u64::MAX, LockAct::Refuse => true }
    }

    /// Note what is NOT constrained: `held` and `held_until` may move however
    /// the implementation likes, because nothing above can see them.
    open spec fn step(a: LockAct, req: Msg, resp: Msg, s0: SrvState, s1: SrvState) -> bool {
        match a {
            LockAct::Grant => {
                &&& s0.hi < u64::MAX
                &&& resp == Msg::Granted((s0.hi + 1) as u64)
                &&& s1.hi == s0.hi + 1
            }
            LockAct::Refuse => resp is Denied && s1.hi == s0.hi,
        }
    }
}

/// The refinement itself.
pub struct LockRef;

impl Refines<LockLo, LockHi> for LockRef {
    /// The mapping: keep the lease counter, discard the clock and the holder.
    open spec fn abs_state(s: SrvState) -> u64 { s.hi }

    /// Both actions stay visible; neither is a stuttering step.
    open spec fn abs_act(a: LockAct) -> Option<LockAct> { Some(a) }

    open spec fn abs_msg(m: Msg) -> Msg { m }

    proof fn lemma_inv(s: SrvState) { }

    /// Civl 3.1(1). The two gates coincide once the mapping is applied, so an
    /// abstract grant is offered exactly where a concrete one succeeds.
    proof fn lemma_gate(a: LockAct, req: Msg, s: SrvState) { }

    /// Civl 3.1(2). Issuing `hi + 1` is a case of issuing something higher.
    proof fn lemma_step(a: LockAct, req: Msg, resp: Msg, s0: SrvState, s1: SrvState) {
        match a {
            LockAct::Grant => {
                assert(resp->Granted_0 == s0.hi + 1);
                assert(resp->Granted_0 > Self::abs_state(s0));
            }
            LockAct::Refuse => { }
        }
    }
}

/// The refinement, transported: every step the implementation takes is a step
/// the abstract server could have taken.
pub proof fn server_step_lifts(
    a: LockAct, req: Msg, resp: Msg, s0: SrvState, s1: SrvState,
)
    requires
        LockLo::step(a, req, resp, s0, s1),
        LockHi::gate(a, req, LockRef::abs_state(s0)),
    ensures
        LockHi::step(a, req, resp, LockRef::abs_state(s0), LockRef::abs_state(s1)),
{
    lift::<LockLo, LockHi, LockRef>(a, req, resp, s0, s1);
}

/// The chain, end to end: whatever step the running server just took, the
/// abstract server could have taken it.
///
/// `serve_one` establishes the premise. Nothing here mentions the clock, the
/// lease, or the holder, because the mapping has already discarded them.
pub proof fn serve_one_is_abstract(pre: LockServer, post: LockServer, resp: Msg)
    requires
        exists|a: LockAct| #[trigger] LockLo::step(
            a, Msg::Acquire, resp, pre.st(), post.st()),
    ensures
        exists|a: LockAct| #[trigger] LockHi::step(
            a, Msg::Acquire, resp,
            LockRef::abs_state(pre.st()), LockRef::abs_state(post.st())),
{
    let a = choose|a: LockAct| LockLo::step(a, Msg::Acquire, resp, pre.st(), post.st());
    // The abstract gate holds: a concrete grant only happens where one is
    // offered, and a refusal never fails.
    match a {
        LockAct::Grant  => { assert(pre.st().hi < u64::MAX); }
        LockAct::Refuse => { }
    }
    server_step_lifts(a, Msg::Acquire, resp, pre.st(), post.st());
    assert(LockHi::step(a, Msg::Acquire, resp,
        LockRef::abs_state(pre.st()), LockRef::abs_state(post.st())));
}

/// The lock server, as an implementation rather than an idealisation: it tracks
/// the outstanding lease and refuses while that lease is still live.
///
/// It waits on every writer at once, so a silent writer does not stop it
/// serving the others.
pub struct LockServer {
    pub inbox: Inbox<Msg, Lease>,
    pub rsps:  FanOut<Msg, Lease>,
    /// The highest lease issued so far; 0 before any. Never reused: when it
    /// cannot advance, the server stops issuing leases rather than repeating
    /// one. Tokens are therefore nonzero without a separate invariant.
    pub hi: u64,
    /// The outstanding lease, if any, and when it runs out.
    pub held: bool,
    pub held_until: u64,
}

impl LockServer {
    pub open spec fn inv(&self) -> bool {
        &&& self.inbox.wf() && self.rsps.wf()
        &&& self.inbox.len() == self.rsps.len()
        &&& self.rsps.len() > 0
        // The reply channels, as one equality between values.
        &&& self.rsps.ids@ =~= Seq::new(self.rsps.len(), |j: int| acq_rsp(j))
        // And the request channels the same way.
        &&& self.inbox.ids@ =~= Seq::new(self.inbox.len(), |k: int| acq_req(k))
    }

    /// This service, seen as the implementation transition system above.
    pub open spec fn st(&self) -> SrvState {
        SrvState { hi: self.hi, held: self.held, held_until: self.held_until }
    }

    /// Serve one acquire, from whichever writer asks first.
    ///
    /// The postcondition is the REFINEMENT: whatever the clock said and whatever
    /// this server's lease bookkeeping decided, the step it just took is one of
    /// the abstract server's two actions. Everything downstream -- in
    /// particular the storage node's write serialization -- depends only on
    /// this, so it holds for any server refining it, including one whose lease
    /// logic is wrong.
    pub fn serve_one(&mut self) -> (k: usize)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            k < final(self).rsps.len(),
            final(self).rsps.len() == old(self).rsps.len(),
            // THE REFINEMENT OBLIGATION: whatever the clock said and whatever
            // this server's lease bookkeeping decided, the step just taken is a
            // step of `LockLo`, and therefore -- by `server_step_lifts` -- one
            // the abstract server could have taken.
            ({
                let h0 = old(self).rsps.hist(k as int);
                let h1 = final(self).rsps.hist(k as int);
                &&& h1 == h0.push(h1.last())
                &&& exists|a: LockAct| #[trigger] LockLo::step(
                        a, Msg::Acquire, h1.last(), old(self).st(), final(self).st())
            }),
            // No other writer's reply channel moved.
            forall|j: int| 0 <= j < final(self).rsps.len() && j != k as int
                ==> #[trigger] final(self).rsps.hist(j) == old(self).rsps.hist(j),
    {
        let ghost pre_st = self.st();

        // The interference point: any writer may ask while we wait.
        let (k, _req) = self.inbox.recv_any();
        let ghost h0 = self.rsps.hist(k as int);

        let now = clock_now();
        let expired = !self.held || now >= self.held_until;

        if expired && self.hi < u64::MAX {
            let t = self.hi + 1;
            self.rsps.send(k, Msg::Granted(t));
            self.hi = t;
            self.held = true;
            // Saturating, because the clock is arbitrary and this is only a
            // deadline, never a token.
            self.held_until = if now <= u64::MAX - LEASE { now + LEASE } else { u64::MAX };
            proof {
                let h1 = self.rsps.hist(k as int);
                assert(h1.last() == Msg::Granted(t));
                assert(h1 == h0.push(h1.last()));
                assert(LockLo::step(LockAct::Grant, Msg::Acquire, h1.last(),
                                    pre_st, self.st()));
                assert(exists|a: LockAct| #[trigger] LockLo::step(
                    a, Msg::Acquire, h1.last(), pre_st, self.st()));
            }
        } else {
            // Either the outstanding lease is still live, or there are no
            // tokens left. The server refuses; it does not reissue.
            self.rsps.send(k, Msg::Denied);
            proof {
                let h1 = self.rsps.hist(k as int);
                assert(h1.last() == Msg::Denied);
                assert(h1 == h0.push(h1.last()));
                assert(LockLo::step(LockAct::Refuse, Msg::Acquire, h1.last(),
                                    pre_st, self.st()));
                assert(exists|a: LockAct| #[trigger] LockLo::step(
                    a, Msg::Acquire, h1.last(), pre_st, self.st()));
            }
        }

        k
    }
}

impl Process for LockServer {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { let _k = self.serve_one(); }
}

/// The storage node. Accepts a write only if its (token, sequence) strictly
/// exceeds every write already accepted, and appends accepted writes to the
/// journal.
///
/// It is the only sender on the journal, so it owns that history, and the
/// ordering it maintains is a fact about state it holds rather than something
/// it needs any other service to cooperate on.
pub struct StorageNode {
    pub reqs: FanIn<Msg, Lease>,
    pub rsps: FanOut<Msg, Lease>,
    pub jrn:  Out<Msg, Lease>,
    pub hi_token: u64,
    pub hi_seq:   u64,
    pub have_any: bool,
    pub turn: usize,
}

impl StorageNode {
    pub open spec fn inv(&self) -> bool {
        &&& self.reqs.len() == self.rsps.len()
        &&& self.reqs.len() > 0
        &&& self.turn < self.reqs.len()
        &&& self.jrn.wf() && self.jrn.id() == journal()
        &&& self.reqs.wf() && self.rsps.wf()
        &&& self.reqs.ids@ =~= Seq::new(self.reqs.len(), |j: int| wr_req(j))
        &&& self.rsps.ids@ =~= Seq::new(self.reqs.len(), |j: int| wr_rsp(j))
        &&& self.reqs.iid() == self.jrn.iid()
        &&& self.rsps.iid() == self.jrn.iid()
        // The node's own invariant: WRITE SERIALIZATION, plus the high-water
        // mark being the last entry.
        &&& serialized(self.jrn.hist())
        &&& self.have_any == (self.jrn.hist().len() > 0)
        &&& self.have_any ==> {
                let last = self.jrn.hist()[self.jrn.hist().len() - 1];
                last->Accepted_0 == self.hi_token && last->Accepted_1 == self.hi_seq
            }
        &&& forall|x: int| 0 <= x < self.jrn.hist().len()
                ==> (#[trigger] self.jrn.hist()[x]) is Accepted
    }

    /// Handle one write from writer `k`.
    pub fn handle_write(&mut self, k: usize)
        requires old(self).inv(), k < old(self).reqs.len(),
        ensures  final(self).inv(), final(self).reqs.len() == old(self).reqs.len(),
    {
        // The interference point.
        let (req, Tracked(rw)) = self.reqs.recv_wit(k);
        proof {
            // The cross-channel step: the token in this request was issued by
            // the server. Nothing in the message itself says so.
            assert(seq![k as int][0] == k as int);
            self.jrn.inst.borrow().learn_cause(wr_req(k as int), rw.element().1, req, &rw);
        }

        // `wit_inv` says a request channel carries only `Write`, so the other
        // arms are unreachable -- they prove `false`.
        let (t, q, v) = match req {
            Msg::Write(t, q, v) => (t, q, v),
            _ => { proof { assert(false); } (0, 0, 0) }
        };

        // The fencing check, against the high-water mark.
        let fresh = !self.have_any || t > self.hi_token
                    || (t == self.hi_token && q > self.hi_seq);

        if fresh {
            let ghost before = self.jrn.hist();
            proof {
                // Every existing entry is below the high-water mark, which the
                // new one exceeds, so the journal stays ordered.
                assert forall|x: int| 0 <= x < before.len()
                    implies lex_lt(#[trigger] before[x], Msg::Accepted(t, q, v)) by {
                    if x < before.len() - 1 {
                        assert(lex_lt(before[x], before[before.len() - 1]));
                    }
                }
                assert forall|x: int, y: int|
                    0 <= x < y < before.push(Msg::Accepted(t, q, v)).len()
                    implies lex_lt(#[trigger] before.push(Msg::Accepted(t, q, v))[x],
                                   #[trigger] before.push(Msg::Accepted(t, q, v))[y]) by {
                    if y < before.len() {
                        assert(before.push(Msg::Accepted(t, q, v))[x] == before[x]);
                        assert(before.push(Msg::Accepted(t, q, v))[y] == before[y]);
                    } else {
                        assert(before.push(Msg::Accepted(t, q, v))[x] == before[x]);
                        assert(before.push(Msg::Accepted(t, q, v))[y] == Msg::Accepted(t, q, v));
                    }
                }
            }
            self.jrn.send(Msg::Accepted(t, q, v));
            self.rsps.send(k, Msg::Accepted(t, q, v));
            self.hi_token = t;
            self.hi_seq = q;
            self.have_any = true;
        } else {
            // A stale lease. The writer is not told why.
            self.rsps.send(k, Msg::Refused);
        }

    }
}

impl Process for StorageNode {
    open spec fn wf(&self) -> bool { self.inv() }

    fn step(&mut self) {
        let k = self.turn;
        self.turn = if k + 1 < self.reqs.count() { k + 1 } else { 0 };
        self.handle_write(k);
    }
}

/// Which phase of its own protocol the writer is in.
///
/// This is what "a client is a state machine" means concretely: the state that
/// used to live between two blocking receives inside one activity is now a
/// field, and the two receives are two handler cases.
pub enum WPhase { Idle, AwaitingGrant, Holding, AwaitingAck }

/// A writer. Acquires a lease, then writes repeatedly under it.
///
/// Written as a HANDLER, so it never blocks: `tick` sends, the driver waits,
/// `handle` reacts. That is also the RPC pattern in this framework -- request,
/// interference point with the invariant checked across it, reply. It needs no
/// atomicity argument, because everything this service knows is either in a
/// token nobody else can hold or in the monotone record of what was sent.
///
/// Note what it still does NOT do: check whether its lease is valid. Between
/// any two of its writes another writer may have been granted a higher token;
/// this one is simply refused from then on.
pub struct Writer {
    pub id:  usize,
    pub acq: Out<Msg, Lease>,
    pub wr:  Out<Msg, Lease>,
    /// The lease held, or 0 for none.
    pub token: u64,
    /// The next sequence number to use under that lease.
    pub seq: u64,
    pub val: u64,
    pub last_ok: bool,
    pub phase: WPhase,
    /// The witness for the grant that issued `token`, kept across writes
    /// because every write must present it.
    pub lease: Tracked<Option<NetSM::was_sent<Msg, Lease>>>,
}

impl NetHandler<Msg, Lease> for Writer {
    open spec fn iid(&self) -> InstanceId { self.wr.iid() }

    /// Slot 0 is the grant channel, slot 1 the acknowledgement channel.
    open spec fn chans(&self) -> Seq<ChanId> {
        seq![acq_rsp(self.id as int), wr_rsp(self.id as int)]
    }

    open spec fn wf(&self) -> bool {
        &&& self.acq.wf() && self.wr.wf()
        &&& self.acq.id() == acq_req(self.id as int)
        &&& self.wr.id()  == wr_req(self.id as int)
        &&& self.acq.iid() == self.wr.iid()
        &&& self.token != 0 ==> {
                &&& self.lease@ is Some
                &&& self.lease@->Some_0.instance_id() == self.wr.iid()
                &&& self.lease@->Some_0.element().0 == acq_rsp(self.id as int)
                &&& self.lease@->Some_0.element().2 == Msg::Granted(self.token)
            }
    }

    fn tick(&mut self) {
        match self.phase {
            WPhase::Idle => {
                self.acq.send(Msg::Acquire);
                self.phase = WPhase::AwaitingGrant;
            }
            WPhase::Holding => {
                if self.token != 0 && self.seq < u64::MAX {
                    let tracked gw;
                    proof { gw = (self.lease.borrow()).tracked_borrow(); }
                    let t = self.token;
                    let q = self.seq;
                    proof { assert(self.wr.id().ix[0] == self.id as int); }
                    self.wr.send_caused(Msg::Write(t, q, self.val), Tracked(gw));
                    self.phase = WPhase::AwaitingAck;
                }
            }
            _ => { }
        }
    }

    fn handle(&mut self, from: usize, m: Msg, Tracked(w): Tracked<NetSM::was_sent<Msg, Lease>>) {
        proof { assert(seq![acq_rsp(self.id as int), wr_rsp(self.id as int)][0]
                       == acq_rsp(self.id as int)); }
        if from == 0 {
            // The grant channel. No run-time check that the token is nonzero:
            // `wit_inv` on this channel already says so, and the driver's
            // precondition says this witness came from it.
            match m {
                Msg::Granted(t) => {
                    self.token = t;
                    self.seq = 0;
                    proof { self.lease = Tracked(Some(w)); }
                    self.phase = WPhase::Holding;
                }
                _ => { self.phase = WPhase::Idle; }
            }
        } else {
            // The acknowledgement channel.
            match m {
                Msg::Accepted(_, _, _) => {
                    self.last_ok = true;
                    if self.seq < u64::MAX { self.seq = self.seq + 1; }
                    self.phase = WPhase::Holding;
                }
                _ => { self.last_ok = false; self.phase = WPhase::Holding; }
            }
        }
    }
}

} // verus!
