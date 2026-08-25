// ABD ATOMICITY, via happens-before.
//
// `abd.rs` proves integrity -- every value returned was really written under
// that tag -- and records why atomicity is out of reach: the argument needs
// "replica r had already stored the tag when it answered the read", and which
// of r's own log entries came first depends on when the read happened relative
// to the write. That is real time, and no message record says it.
//
// THIS FILE SAYS IT, and the claim to test is that no framework change is
// needed. Happens-before is built from two things the development already has:
//
//   * a gate on one channel, forcing an owned log's CLOCKS to strictly
//     increase, so clock order and position order agree; and
//   * a provenance obligation, forcing every cause's clock to be below its
//     effect's, so a chain of causes is a chain of increasing clocks.
//
// Composed, those give exactly Lamport's relation, and it crosses participants
// because provenance does.
//
// Scope: one client, which writes and then reads, so "the read began after the
// write completed" is an ordering WITHIN the client's own log. The write-back
// phase is omitted -- it exists for atomicity between concurrent readers, which
// a single sequential client does not have.
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::tok::*;
use crate::proc::*;
use crate::quorum::*;

verus! {

// ---------------------------------------------------------------------------
// Replicas and quorums
// ---------------------------------------------------------------------------

pub uninterp spec fn n_rep() -> int;

#[verifier::external_body]
pub proof fn rep_config()
    ensures n_rep() >= 1,
{
}

pub open spec fn reps() -> Set<int> { set_int_range(0, n_rep()) }

pub proof fn lemma_reps()
    ensures reps().len() == n_rep(),
            forall|r: int| reps().contains(r) <==> 0 <= r < n_rep(),
{
    rep_config();
    lemma_int_range(0, n_rep());
}

pub open spec fn is_quorum(q: Set<int>) -> bool {
    q.subset_of(reps()) && q.len() + q.len() > n_rep()
}

pub proof fn lemma_quorum_intersect(q1: Set<int>, q2: Set<int>)
    requires is_quorum(q1), is_quorum(q2),
    ensures  exists|r: int| q1.contains(r) && q2.contains(r),
{
    lemma_reps();
    lemma_quorums_intersect(reps(), q1, q2);
}

// ---------------------------------------------------------------------------
// Channels and messages
// ---------------------------------------------------------------------------

/// The client's own log: everything it does, in order. Writing and reading are
/// both here, which is what makes "the read began after the write completed" a
/// fact about ONE history.
pub open spec fn clog() -> ChanId { chan(0, seq![]) }
/// Replica `r`'s own log: what it stored, what reads it saw, what it answered.
pub open spec fn rlog(r: int) -> ChanId { chan(1, seq![r]) }
/// Client to replica and back, for writes and for reads.
pub open spec fn wch(r: int) -> ChanId { chan(2, seq![r]) }
pub open spec fn ach(r: int) -> ChanId { chan(3, seq![r]) }
pub open spec fn qch(r: int) -> ChanId { chan(4, seq![r]) }
pub open spec fn sch(r: int) -> ChanId { chan(5, seq![r]) }

#[derive(Structural, PartialEq, Eq)]
pub enum HMsg {
    /// Client log.
    WVal(u64, u64, u64),    // tag, value, clock
    WDone(u64, u64),        // tag, clock
    RStart(u64),            // clock
    Return(u64, u64, u64, u64), // tag, value, round, clock
    /// Wire.
    Write(u64, u64, u64),
    Ack(u64, u64),
    /// The read phase carries a ROUND ID -- the clock of the `RStart` that
    /// began it. Without it, a reply could be matched to the wrong read, and
    /// the ordering chain would not close.
    Read(u64, u64),         // round, clock
    Value(u64, u64, u64, u64),  // tag, value, round, clock
    /// Replica log.
    Store(u64, u64, u64),
    Got(u64, u64),          // round, clock
    Rep(u64, u64, u64, u64),    // tag, value, round, clock
}

/// THE CLOCK of any message. Every message carries one; this is what makes the
/// ordering uniform across channels.
pub open spec fn clk(m: HMsg) -> u64 {
    match m {
        HMsg::WVal(_, _, c)   => c,
        HMsg::WDone(_, c)     => c,
        HMsg::RStart(c)       => c,
        HMsg::Return(_, _, _, c) => c,
        HMsg::Write(_, _, c)  => c,
        HMsg::Ack(_, c)       => c,
        HMsg::Read(_, c)      => c,
        HMsg::Value(_, _, _, c) => c,
        HMsg::Store(_, _, c)  => c,
        HMsg::Got(_, c)       => c,
        HMsg::Rep(_, _, _, c) => c,
    }
}

/// The round a read-phase message belongs to.
pub open spec fn rnd(m: HMsg) -> u64 {
    match m {
        HMsg::Read(r, _)       => r,
        HMsg::Got(r, _)        => r,
        HMsg::Rep(_, _, r, _)  => r,
        HMsg::Value(_, _, r, _) => r,
        HMsg::Return(_, _, r, _) => r,
        _ => 0,
    }
}

pub open spec fn is_rlog(c: ChanId) -> bool { c == rlog(c.ix[0]) }
pub open spec fn is_wch(c: ChanId)  -> bool { c == wch(c.ix[0]) }
pub open spec fn is_ach(c: ChanId)  -> bool { c == ach(c.ix[0]) }
pub open spec fn is_qch(c: ChanId)  -> bool { c == qch(c.ix[0]) }
pub open spec fn is_sch(c: ChanId)  -> bool { c == sch(c.ix[0]) }

pub proof fn lemma_shapes(r: int)
    ensures
        is_rlog(rlog(r)), rlog(r).ix[0] == r,
        is_wch(wch(r)),   wch(r).ix[0] == r,
        is_ach(ach(r)),   ach(r).ix[0] == r,
        is_qch(qch(r)),   qch(r).ix[0] == r,
        is_sch(sch(r)),   sch(r).ix[0] == r,
{
    assert(seq![r][0] == r);
}

/// A log whose clocks strictly increase. Stated over one history, so a gate can
/// enforce it and `history_inv` can carry it.
pub open spec fn clocks_increase(h: Seq<HMsg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len() ==> clk(#[trigger] h[x]) < clk(#[trigger] h[y])
}

/// The highest tag this replica had stored by the time it had written `k`
/// entries -- `0` if it had stored nothing.
pub open spec fn stored_upto(h: Seq<HMsg>, k: int) -> u64
    decreases k
{
    if k <= 0 { 0 }
    else if h[k - 1] is Store { h[k - 1]->Store_0 }
    else { stored_upto(h, k - 1) }
}

pub struct AbdHb;

pub open spec fn is_log(c: ChanId) -> bool { c == clog() || is_rlog(c) }

// ---------------------------------------------------------------------------
// The record invariant
// ---------------------------------------------------------------------------

/// One position of one channel holds one message, from the machine's own
/// `agree` invariant.
pub open spec fn rec_functional(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m1: HMsg, m2: HMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, i, m2)))
            ==> m1 == m2
}

/// HAPPENS-BEFORE WITHIN A LOG. Positions and clocks agree, so comparing two
/// clocks decides which of two entries on the same channel came first. This is
/// the whole content of the gate, lifted to the record.
pub open spec fn rec_clock_order(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, j: nat, m1: HMsg, m2: HMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, j, m2)))
        && is_log(c) && i < j ==> clk(m1) < clk(m2)
}

/// A reply never under-reports what the replica had already stored.
pub open spec fn rec_rep_dominates(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, k: nat, ms: HMsg, mr: HMsg|
        (#[trigger] ws.contains((c, i, ms))) && (#[trigger] ws.contains((c, k, mr)))
        && is_rlog(c) && i < k && ms is Store && mr is Rep
            ==> ms->Store_0 <= mr->Rep_0
}

// HAPPENS-BEFORE ACROSS PARTICIPANTS. Each clause is one provenance edge, and
// each carries the same extra word: the cause's clock is below the effect's.

pub open spec fn rec_ack_after_store(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_ach(c)
            ==> exists|j: nat, ms: HMsg| ws.contains((rlog(c.ix[0]), j, ms))
                    && ms is Store && ms->Store_0 == m->Ack_0 && clk(ms) < clk(m)
}

pub open spec fn rec_got_after_read(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_rlog(c) && m is Got
            ==> exists|j: nat, mq: HMsg| ws.contains((qch(c.ix[0]), j, mq))
                    && mq is Read && rnd(mq) == rnd(m) && clk(mq) < clk(m)
}

pub open spec fn rec_read_after_rstart(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_qch(c)
            ==> exists|j: nat, mr: HMsg| ws.contains((clog(), j, mr))
                    && mr is RStart && clk(mr) == rnd(m) && clk(mr) < clk(m)
}

pub open spec fn rec_rep_after_got(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_rlog(c) && m is Rep
            ==> exists|j: nat, mg: HMsg| ws.contains((c, j, mg))
                    && mg is Got && rnd(mg) == rnd(m) && clk(mg) < clk(m)
}

pub open spec fn rec_value_after_rep(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_sch(c)
            ==> exists|j: nat, mp: HMsg| ws.contains((rlog(c.ix[0]), j, mp))
                    && mp is Rep && mp->Rep_0 == m->Value_0
                    && rnd(mp) == rnd(m) && clk(mp) < clk(m)
}

/// Replica `r` acknowledged tag `t`.
pub open spec fn acked(ws: Set<(ChanId, nat, HMsg)>, r: int, t: u64, hi: u64) -> bool {
    exists|i: nat, c: u64| ws.contains((ach(r), i, HMsg::Ack(t, c))) && c < hi
}

/// A completed write: a quorum acknowledged it.
pub open spec fn rec_wdone_quorum(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|i: nat, m: HMsg|
        (#[trigger] ws.contains((clog(), i, m))) && m is WDone
            ==> exists|q: Set<int>| is_quorum(q)
                    && forall|r: int| q.contains(r) ==> acked(ws, r, m->WDone_0, clk(m))
}

/// Replica `r` answered a read with tag `tr`, at a clock above `lo`.
pub open spec fn answered(ws: Set<(ChanId, nat, HMsg)>, r: int, tr: u64, rid: u64) -> bool {
    exists|i: nat, v: u64, cv: u64| ws.contains((sch(r), i, HMsg::Value(tr, v, rid, cv)))
}

/// A return: a quorum answered, every answer is at most the tag returned, and
/// they all answered AFTER the read started. The last clause is what ties this
/// return to one read rather than to any reply ever sent.
pub open spec fn rec_return_quorum(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|i: nat, m: HMsg|
        (#[trigger] ws.contains((clog(), i, m))) && m is Return
            ==> exists|q: Set<int>| is_quorum(q)
                    && forall|r: int| q.contains(r)
                            ==> exists|tr: u64| tr <= m->Return_0 && answered(ws, r, tr, rnd(m))
}

impl NetInv<HMsg> for AbdHb {
    /// Every log's clocks strictly increase. That single clause is the whole of
    /// happens-before within a participant, and it is checkable because it
    /// mentions only this channel's own history.
    open spec fn gate(c: ChanId, s: Seq<HMsg>, m: HMsg) -> bool {
        &&& (is_log(c) ==> forall|x: int| 0 <= x < s.len() ==> clk(#[trigger] s[x]) < clk(m))
        &&& (c == clog() ==> m is WVal || m is WDone || m is RStart || m is Return)
        &&& (is_rlog(c) ==> {
                &&& (m is Store || m is Got || m is Rep)
                // A replica never goes backwards ...
                &&& (m is Store ==> forall|x: int| 0 <= x < s.len() && (#[trigger] s[x]) is Store
                        ==> s[x]->Store_0 < m->Store_0)
                // ... and never under-reports what it holds.
                &&& (m is Rep ==> forall|x: int| 0 <= x < s.len() && (#[trigger] s[x]) is Store
                        ==> s[x]->Store_0 <= m->Rep_0)
            })
        &&& (is_wch(c) ==> m is Write)
        &&& (is_ach(c) ==> m is Ack)
        &&& (is_qch(c) ==> m is Read)
        &&& (is_sch(c) ==> m is Value)
    }

    open spec fn wit_inv(c: ChanId, m: HMsg) -> bool {
        &&& (forall|r: int| c == #[trigger] wch(r) ==> m is Write)
        &&& (forall|r: int| c == #[trigger] ach(r) ==> m is Ack)
        &&& (forall|r: int| c == #[trigger] qch(r) ==> m is Read)
        &&& (forall|r: int| c == #[trigger] sch(r) ==> m is Value)
    }

    open spec fn deliverable_at(v: Seq<HMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn history_inv(sent: Map<ChanId, Seq<HMsg>>) -> bool { true }
    open spec fn pair_gives(c: ChanId, m1: HMsg, m2: HMsg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<HMsg>>, c: ChanId,
                              i: nat, j: nat, m1: HMsg, m2: HMsg) { }
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<HMsg>, m: HMsg) {
        assert forall|r: int| c == #[trigger] wch(r) implies m is Write by { assert(seq![r][0] == r); }
        assert forall|r: int| c == #[trigger] ach(r) implies m is Ack by { assert(seq![r][0] == r); }
        assert forall|r: int| c == #[trigger] qch(r) implies m is Read by { assert(seq![r][0] == r); }
        assert forall|r: int| c == #[trigger] sch(r) implies m is Value by { assert(seq![r][0] == r); }
    }
    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<HMsg>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<HMsg>>,
                                         was_sent: Set<(ChanId, nat, HMsg)>,
                                         c: ChanId, s: Seq<HMsg>, m: HMsg,
                                         causes: Set<(ChanId, nat, HMsg)>) { }

    /// Six edges. Each says the same thing twice: what caused this, and that it
    /// happened first.
    open spec fn needs_cause(c: ChanId, m: HMsg) -> bool {
        ||| is_ach(c)
        ||| is_qch(c)
        ||| is_sch(c)
        ||| (is_rlog(c) && m is Got)
        ||| (is_rlog(c) && m is Rep)
        ||| (c == clog() && (m is WDone || m is Return))
    }

    open spec fn caused_by(c: ChanId, m: HMsg, causes: Set<(ChanId, nat, HMsg)>) -> bool {
        &&& (is_ach(c) ==> exists|j: nat, ms: HMsg| causes.contains((rlog(c.ix[0]), j, ms))
                && ms is Store && ms->Store_0 == m->Ack_0 && clk(ms) < clk(m))
        &&& (is_qch(c) ==> exists|j: nat, mr: HMsg| causes.contains((clog(), j, mr))
                && mr is RStart && clk(mr) == rnd(m) && clk(mr) < clk(m))
        &&& (is_sch(c) ==> exists|j: nat, mp: HMsg| causes.contains((rlog(c.ix[0]), j, mp))
                && mp is Rep && mp->Rep_0 == m->Value_0
                && rnd(mp) == rnd(m) && clk(mp) < clk(m))
        &&& (is_rlog(c) && m is Got ==> exists|j: nat, mq: HMsg| causes.contains((qch(c.ix[0]), j, mq))
                && mq is Read && rnd(mq) == rnd(m) && clk(mq) < clk(m))
        &&& (is_rlog(c) && m is Rep ==> exists|j: nat, mg: HMsg| causes.contains((c, j, mg))
                && mg is Got && rnd(mg) == rnd(m) && clk(mg) < clk(m))
        &&& (c == clog() && m is WDone ==> exists|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r) ==> acked(causes, r, m->WDone_0, clk(m)))
        &&& (c == clog() && m is Return ==> exists|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r)
                        ==> exists|tr: u64| tr <= m->Return_0 && answered(causes, r, tr, rnd(m)))
    }

    open spec fn caused_by1(c: ChanId, m: HMsg, d: ChanId, j: nat, m2: HMsg) -> bool {
        &&& (is_ach(c) ==> d == rlog(c.ix[0]) && m2 is Store
                && m2->Store_0 == m->Ack_0 && clk(m2) < clk(m))
        &&& (is_qch(c) ==> d == clog() && m2 is RStart && clk(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_sch(c) ==> d == rlog(c.ix[0]) && m2 is Rep
                && m2->Rep_0 == m->Value_0 && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_rlog(c) && m is Got ==> d == qch(c.ix[0]) && m2 is Read
                && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_rlog(c) && m is Rep ==> d == c && m2 is Got
                && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& !(c == clog() && (m is WDone || m is Return))
    }

    proof fn lemma_caused_by1(c: ChanId, m: HMsg, d: ChanId, j: nat, m2: HMsg) {
        let cs = set![(d, j, m2)];
        assert(cs.contains((d, j, m2)));
    }

    open spec fn caused_by2(c: ChanId, m: HMsg, d1: ChanId, j1: nat, m1: HMsg,
                            d2: ChanId, j2: nat, m2: HMsg) -> bool { false }
    proof fn lemma_caused_by2(c: ChanId, m: HMsg, d1: ChanId, j1: nat, m1: HMsg,
                              d2: ChanId, j2: nat, m2: HMsg) { }

    open spec fn cause_gives(c: ChanId, m: HMsg) -> bool { true }
    proof fn lemma_cause_gives(c: ChanId, m: HMsg, causes: Set<(ChanId, nat, HMsg)>) { }

    open spec fn record_inv(ws: Set<(ChanId, nat, HMsg)>) -> bool {
        &&& rec_functional(ws)
        &&& rec_clock_order(ws)
        &&& rec_rep_dominates(ws)
        &&& rec_ack_after_store(ws)
        &&& rec_got_after_read(ws)
        &&& rec_read_after_rstart(ws)
        &&& rec_rep_after_got(ws)
        &&& rec_value_after_rep(ws)
        &&& rec_wdone_quorum(ws)
        &&& rec_return_quorum(ws)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, HMsg)>,
                                        sent: Map<ChanId, Seq<HMsg>>,
                                        c: ChanId, s: Seq<HMsg>, m: HMsg,
                                        causes: Set<(ChanId, nat, HMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

        // Every entry already recorded sits at a position of the history the
        // gate just read, so it is BELOW the new one. That single fact settles
        // the three clauses about positions.
        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] was_sent.contains((k, x, mm))) && k == c implies x < s.len() by { }

        // ---- one position, one message ----
        assert forall|k: ChanId, x: nat, m1: HMsg, m2: HMsg|
            (#[trigger] post.contains((k, x, m1))) && (#[trigger] post.contains((k, x, m2)))
            implies m1 == m2 by {
            if (k, x, m1) == e && (k, x, m2) != e { assert(was_sent.contains((k, x, m2))); }
            if (k, x, m2) == e && (k, x, m1) != e { assert(was_sent.contains((k, x, m1))); }
        }

        // ---- clocks increase with position, in every log ----
        assert forall|k: ChanId, x: nat, y: nat, m1: HMsg, m2: HMsg|
            (#[trigger] post.contains((k, x, m1))) && (#[trigger] post.contains((k, y, m2)))
            && is_log(k) && x < y implies clk(m1) < clk(m2) by {
            if (k, y, m2) == e {
                assert(was_sent.contains((k, x, m1)));
                assert(x < s.len() && sent[k][x as int] == m1);
                assert(clk(s[x as int]) < clk(m));
            }
        }

        // ---- a reply dominates every store before it ----
        assert forall|k: ChanId, x: nat, y: nat, ms: HMsg, mr: HMsg|
            (#[trigger] post.contains((k, x, ms))) && (#[trigger] post.contains((k, y, mr)))
            && is_rlog(k) && x < y && ms is Store && mr is Rep
            implies ms->Store_0 <= mr->Rep_0 by {
            if (k, y, mr) == e {
                assert(was_sent.contains((k, x, ms)));
                assert(x < s.len() && sent[k][x as int] == ms);
                assert(s[x as int]->Store_0 <= m->Rep_0);
            }
        }

        // ---- the five single-cause edges ----
        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_ach(k)
            implies exists|j: nat, ms: HMsg| post.contains((rlog(k.ix[0]), j, ms))
                && ms is Store && ms->Store_0 == mm->Ack_0 && clk(ms) < clk(mm) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (j0, ms0) = choose|j: nat, ms: HMsg| causes.contains((rlog(c.ix[0]), j, ms))
                    && ms is Store && ms->Store_0 == m->Ack_0 && clk(ms) < clk(m);
                assert(post.contains((rlog(k.ix[0]), j0, ms0)));
            } else {
                let (j0, ms0) = choose|j: nat, ms: HMsg| was_sent.contains((rlog(k.ix[0]), j, ms))
                    && ms is Store && ms->Store_0 == mm->Ack_0 && clk(ms) < clk(mm);
                assert(post.contains((rlog(k.ix[0]), j0, ms0)));
            }
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rlog(k) && mm is Got
            implies exists|j: nat, mq: HMsg| post.contains((qch(k.ix[0]), j, mq))
                && mq is Read && rnd(mq) == rnd(mm) && clk(mq) < clk(mm) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (j0, mq0) = choose|j: nat, mq: HMsg| causes.contains((qch(c.ix[0]), j, mq))
                    && mq is Read && rnd(mq) == rnd(m) && clk(mq) < clk(m);
                assert(post.contains((qch(k.ix[0]), j0, mq0)));
            } else {
                let (j0, mq0) = choose|j: nat, mq: HMsg| was_sent.contains((qch(k.ix[0]), j, mq))
                    && mq is Read && rnd(mq) == rnd(mm) && clk(mq) < clk(mm);
                assert(post.contains((qch(k.ix[0]), j0, mq0)));
            }
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_qch(k)
            implies exists|j: nat, mr: HMsg| post.contains((clog(), j, mr))
                && mr is RStart && clk(mr) == rnd(mm) && clk(mr) < clk(mm) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (j0, mr0) = choose|j: nat, mr: HMsg| causes.contains((clog(), j, mr))
                    && mr is RStart && clk(mr) == rnd(m) && clk(mr) < clk(m);
                assert(post.contains((clog(), j0, mr0)));
            } else {
                let (j0, mr0) = choose|j: nat, mr: HMsg| was_sent.contains((clog(), j, mr))
                    && mr is RStart && clk(mr) == rnd(mm) && clk(mr) < clk(mm);
                assert(post.contains((clog(), j0, mr0)));
            }
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rlog(k) && mm is Rep
            implies exists|j: nat, mg: HMsg| post.contains((k, j, mg))
                && mg is Got && rnd(mg) == rnd(mm) && clk(mg) < clk(mm) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (j0, mg0) = choose|j: nat, mg: HMsg| causes.contains((c, j, mg))
                    && mg is Got && rnd(mg) == rnd(m) && clk(mg) < clk(m);
                assert(post.contains((k, j0, mg0)));
            } else {
                let (j0, mg0) = choose|j: nat, mg: HMsg| was_sent.contains((k, j, mg))
                    && mg is Got && rnd(mg) == rnd(mm) && clk(mg) < clk(mm);
                assert(post.contains((k, j0, mg0)));
            }
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_sch(k)
            implies exists|j: nat, mp: HMsg| post.contains((rlog(k.ix[0]), j, mp))
                && mp is Rep && mp->Rep_0 == mm->Value_0
                && rnd(mp) == rnd(mm) && clk(mp) < clk(mm) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (j0, mp0) = choose|j: nat, mp: HMsg| causes.contains((rlog(c.ix[0]), j, mp))
                    && mp is Rep && mp->Rep_0 == m->Value_0
                    && rnd(mp) == rnd(m) && clk(mp) < clk(m);
                assert(post.contains((rlog(k.ix[0]), j0, mp0)));
            } else {
                let (j0, mp0) = choose|j: nat, mp: HMsg| was_sent.contains((rlog(k.ix[0]), j, mp))
                    && mp is Rep && mp->Rep_0 == mm->Value_0
                    && rnd(mp) == rnd(mm) && clk(mp) < clk(mm);
                assert(post.contains((rlog(k.ix[0]), j0, mp0)));
            }
        }

        // ---- the two quorum edges ----
        assert forall|x: nat, mm: HMsg|
            (#[trigger] post.contains((clog(), x, mm))) && mm is WDone
            implies exists|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r) ==> acked(post, r, mm->WDone_0, clk(mm)) by {
            let src = if (clog(), x, mm) == e { causes } else { was_sent };
            let q0 = choose|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r) ==> acked(src, r, mm->WDone_0, clk(mm));
            assert forall|r: int| q0.contains(r)
                implies acked(post, r, mm->WDone_0, clk(mm)) by {
                let (ai, ca) = choose|ai: nat, ca: u64|
                    src.contains((ach(r), ai, HMsg::Ack(mm->WDone_0, ca))) && ca < clk(mm);
                assert(post.contains((ach(r), ai, HMsg::Ack(mm->WDone_0, ca))));
            }
        }

        assert forall|x: nat, mm: HMsg|
            (#[trigger] post.contains((clog(), x, mm))) && mm is Return
            implies exists|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r)
                        ==> exists|tr: u64| tr <= mm->Return_0 && answered(post, r, tr, rnd(mm)) by {
            let src = if (clog(), x, mm) == e { causes } else { was_sent };
            let q0 = choose|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r)
                        ==> exists|tr: u64| tr <= mm->Return_0 && answered(src, r, tr, rnd(mm));
            assert forall|r: int| q0.contains(r) implies
                exists|tr: u64| tr <= mm->Return_0 && answered(post, r, tr, rnd(mm)) by {
                let t0 = choose|tr: u64| tr <= mm->Return_0 && answered(src, r, tr, rnd(mm));
                let (vi, vv, cv) = choose|vi: nat, vv: u64, cv: u64|
                    src.contains((sch(r), vi, HMsg::Value(t0, vv, rnd(mm), cv)));
                assert(post.contains((sch(r), vi, HMsg::Value(t0, vv, rnd(mm), cv))));
                assert(answered(post, r, t0, rnd(mm)));
            }
        }
    }
}

impl DetDelivery<HMsg> for AbdHb {
    proof fn lemma_delivery_determined(v: Seq<HMsg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}


/// NOT VACUOUS: the chain has a start.
///
/// `spike/crosschan.rs` was once vacuous because every send demanded a cause
/// and none could ever be discharged, so nothing past `boot` was reachable.
/// Here two sends need no justification -- a replica may store, and the client
/// may begin a read -- and an empty log accepts any clock, so the chain can
/// begin and each later link has something to point at.
pub proof fn lemma_protocol_enabled()
    ensures
        !AbdHb::needs_cause(rlog(0), HMsg::Store(1, 7, 1)),
        !AbdHb::needs_cause(clog(), HMsg::RStart(1)),
        AbdHb::gate(rlog(0), Seq::<HMsg>::empty(), HMsg::Store(1, 7, 1)),
        AbdHb::gate(clog(), Seq::<HMsg>::empty(), HMsg::RStart(1)),
{
    lemma_shapes(0);
    assert(rlog(0) != clog()) by { lemma_chan_distinct(1, seq![0int], 0, seq![]); }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Happens-before, as two lemmas
// ---------------------------------------------------------------------------

/// COMPARING CLOCKS DECIDES ORDER WITHIN A LOG.
///
/// The direction that matters: a bigger clock means a later position. This is
/// the contrapositive of the gate, and it is what turns a chain of provenance
/// into a statement about one replica's own history.
pub proof fn lemma_clock_gives_position(
    ws: Set<(ChanId, nat, HMsg)>, c: ChanId, i: nat, j: nat, m1: HMsg, m2: HMsg,
)
    requires
        rec_clock_order(ws), rec_functional(ws), is_log(c),
        ws.contains((c, i, m1)), ws.contains((c, j, m2)),
        clk(m1) < clk(m2),
    ensures
        i < j,
{
    if j < i { assert(clk(m2) < clk(m1)); }
    if i == j { assert(m1 == m2); }
}

/// A REPLICA THAT STORED `t` BEFORE IT ANSWERED, ANSWERS AT LEAST `t`.
///
/// The step `abd.rs` could not take. Everything it needs is now local: both
/// events are in this replica's own log, and their clocks say which came first.
pub proof fn lemma_replica_reports_high(
    ws: Set<(ChanId, nat, HMsg)>, r: int, i: nat, k: nat, ms: HMsg, mp: HMsg,
)
    requires
        rec_clock_order(ws), rec_functional(ws), rec_rep_dominates(ws),
        ws.contains((rlog(r), i, ms)), ms is Store,
        ws.contains((rlog(r), k, mp)), mp is Rep,
        clk(ms) < clk(mp),
    ensures
        ms->Store_0 <= mp->Rep_0,
{
    lemma_shapes(r);
    lemma_clock_gives_position(ws, rlog(r), i, k, ms, mp);
}

/// ATOMICITY.
///
/// A read that began after a write completed returns at least that write's tag.
/// `cw < rid` is the hypothesis, and it is a fact about the CLIENT'S OWN LOG:
/// the client logged `WDone` and then `RStart`, and a log's clocks increase.
pub proof fn lemma_atomicity(
    ws: Set<(ChanId, nat, HMsg)>,
    t: u64, cw: u64, pw: nat,
    tr: u64, vr: u64, rid: u64, cret: u64, pr: nat,
)
    requires
        AbdHb::record_inv(ws),
        ws.contains((clog(), pw, HMsg::WDone(t, cw))),
        ws.contains((clog(), pr, HMsg::Return(tr, vr, rid, cret))),
        // the read started after the write completed
        cw < rid,
    ensures
        t <= tr,
{
    // The write's quorum, and the read's.
    let q1 = choose|q: Set<int>| is_quorum(q)
        && forall|r: int| q.contains(r) ==> acked(ws, r, t, cw);
    let q2 = choose|q: Set<int>| is_quorum(q)
        && forall|r: int| q.contains(r)
                ==> exists|x: u64| x <= tr && answered(ws, r, x, rid);
    lemma_quorum_intersect(q1, q2);
    let r = choose|r: int| q1.contains(r) && q2.contains(r);
    lemma_shapes(r);

    // What `r` did for the write: it stored `t` before acknowledging, and it
    // acknowledged before the write was declared complete.
    let (ai, ca) = choose|ai: nat, ca: u64|
        ws.contains((ach(r), ai, HMsg::Ack(t, ca))) && ca < cw;
    let (si, ms) = choose|si: nat, ms: HMsg| ws.contains((rlog(r), si, ms))
        && ms is Store && ms->Store_0 == t && clk(ms) < ca;

    // What `r` did for the read, in this round: it answered from a `Rep`, which
    // followed a `Got`, which followed the `Read`, which followed the `RStart`
    // whose clock IS the round.
    let x = choose|x: u64| x <= tr && answered(ws, r, x, rid);
    let (vi, vv, cv) = choose|vi: nat, vv: u64, cv: u64|
        ws.contains((sch(r), vi, HMsg::Value(x, vv, rid, cv)));
    let (pi, mp) = choose|pi: nat, mp: HMsg| ws.contains((rlog(r), pi, mp))
        && mp is Rep && mp->Rep_0 == x && rnd(mp) == rid && clk(mp) < cv;
    let (gi, mg) = choose|gi: nat, mg: HMsg| ws.contains((rlog(r), gi, mg))
        && mg is Got && rnd(mg) == rid && clk(mg) < clk(mp);
    let (qi, mq) = choose|qi: nat, mq: HMsg| ws.contains((qch(r), qi, mq))
        && mq is Read && rnd(mq) == rid && clk(mq) < clk(mg);
    let (ri, mr) = choose|ri: nat, mr: HMsg| ws.contains((clog(), ri, mr))
        && mr is RStart && clk(mr) == rid && clk(mr) < clk(mq);

    // The chain: store < ack < write-complete < round < read < got < reply.
    assert(clk(ms) < ca);
    assert(ca < cw);
    assert(cw < rid);
    assert(rid == clk(mr));
    assert(clk(mr) < clk(mq));
    assert(clk(mq) < clk(mg));
    assert(clk(mg) < clk(mp));

    lemma_replica_reports_high(ws, r, si, pi, ms, mp);
}

} // verus!
