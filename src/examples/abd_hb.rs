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
pub open spec fn clog(k: int) -> ChanId { chan(0, seq![k]) }
/// Replica `r`'s own log: what it stored, what reads it saw, what it answered.
pub open spec fn rlog(r: int) -> ChanId { chan(1, seq![r]) }
/// Client to replica and back, for writes and for reads.
pub open spec fn qch(k: int, r: int) -> ChanId { chan(2, seq![k, r, 0]) }
pub open spec fn sch(k: int, r: int) -> ChanId { chan(3, seq![k, r, 0]) }
/// PROPAGATE: the writer's write and a reader's write-back are the same phase,
/// so they share a channel pair. That is not a simplification of ABD -- it is
/// what makes the write-back able to play the write's role in the argument.
pub open spec fn bch(k: int, r: int) -> ChanId { chan(4, seq![k, r, 0]) }
pub open spec fn bach(k: int, r: int) -> ChanId { chan(5, seq![k, r, 0]) }

#[derive(Structural, PartialEq, Eq)]
pub enum HMsg {
    /// Client log.
    WDone(u64, u64, u64),   // tag, round, clock
    RStart(u64),            // clock
    Return(u64, u64, u64, u64), // tag, value, round, clock
    /// Wire: propagate a tagged value, and acknowledge it.
    Prop(u64, u64, u64, u64),   // tag, value, round, clock
    BAck(u64, u64, u64),        // tag, round, clock
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
        HMsg::WDone(_, _, c)  => c,
        HMsg::RStart(c)       => c,
        HMsg::Return(_, _, _, c) => c,
        HMsg::Prop(_, _, _, c) => c,
        HMsg::BAck(_, _, c)   => c,
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
        HMsg::WDone(_, r, _)   => r,
        HMsg::Prop(_, _, r, _) => r,
        HMsg::BAck(_, r, _)    => r,
        HMsg::Read(r, _)       => r,
        HMsg::Got(r, _)        => r,
        HMsg::Rep(_, _, r, _)  => r,
        HMsg::Value(_, _, r, _) => r,
        HMsg::Return(_, _, r, _) => r,
        _ => 0,
    }
}

pub open spec fn is_rlog(c: ChanId) -> bool { c == rlog(c.ix[0]) }
pub open spec fn is_clog(c: ChanId) -> bool { c == clog(c.ix[0]) }
pub open spec fn is_qch(c: ChanId)  -> bool { c == qch(c.ix[0], c.ix[1]) }
pub open spec fn is_sch(c: ChanId)  -> bool { c == sch(c.ix[0], c.ix[1]) }
pub open spec fn is_bch(c: ChanId)  -> bool { c == bch(c.ix[0], c.ix[1]) }
pub open spec fn is_bach(c: ChanId) -> bool { c == bach(c.ix[0], c.ix[1]) }

pub proof fn lemma_shapes(k: int, r: int)
    ensures
        is_rlog(rlog(r)),   rlog(r).ix[0] == r,
        is_clog(clog(k)),   clog(k).ix[0] == k,
        is_qch(qch(k, r)),  qch(k, r).ix[0] == k,  qch(k, r).ix[1] == r,
        is_sch(sch(k, r)),  sch(k, r).ix[0] == k,  sch(k, r).ix[1] == r,
        is_bch(bch(k, r)),  bch(k, r).ix[0] == k,  bch(k, r).ix[1] == r,
        is_bach(bach(k, r)), bach(k, r).ix[0] == k, bach(k, r).ix[1] == r,
{
    assert(seq![r][0] == r);
    assert(seq![k][0] == k);
    assert(seq![k, r, 0][0] == k);
    assert(seq![k, r, 0][1] == r);
}

/// A log whose clocks strictly increase. Stated over one history, so a gate can
/// enforce it and `history_inv` can carry it.
pub open spec fn clocks_increase(h: Seq<HMsg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len() ==> clk(#[trigger] h[x]) < clk(#[trigger] h[y])
}

pub struct AbdHb;

pub open spec fn is_log(c: ChanId) -> bool { is_clog(c) || is_rlog(c) }

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
/// clocks decides which of two entries on the same channel came first.
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

// HAPPENS-BEFORE ACROSS PARTICIPANTS. Each clause is one provenance edge
// carrying the same extra word: the cause's clock is below the effect's.

/// An acknowledgement means the replica had logged a tag at least this high.
pub open spec fn rec_back_after_store(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_bach(c)
            ==> exists|j: nat, ms: HMsg| ws.contains((rlog(c.ix[1]), j, ms))
                    && ms is Store && m->BAck_0 <= ms->Store_0 && clk(ms) < clk(m)
}

pub open spec fn rec_got_after_read(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_rlog(c) && m is Got
            ==> exists|k: int, j: nat, mq: HMsg| ws.contains((qch(k, c.ix[0]), j, mq))
                    && mq is Read && rnd(mq) == rnd(m) && clk(mq) < clk(m)
}

pub open spec fn rec_read_after_rstart(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_qch(c)
            ==> exists|j: nat, mr: HMsg| ws.contains((clog(c.ix[0]), j, mr))
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
            ==> exists|j: nat, mp: HMsg| ws.contains((rlog(c.ix[1]), j, mp))
                    && mp is Rep && mp->Rep_0 == m->Value_0
                    && rnd(mp) == rnd(m) && clk(mp) < clk(m)
}

/// Client `k` had tag `t` acknowledged by replica `r`, in round `rid`, before
/// clock `hi`.
pub open spec fn backed(ws: Set<(ChanId, nat, HMsg)>, k: int, r: int,
                        t: u64, rid: u64, hi: u64) -> bool {
    exists|i: nat, cb: u64| ws.contains((bach(k, r), i, HMsg::BAck(t, rid, cb))) && cb < hi
}

/// Replica `r` answered client `k`'s round `rid` with tag `tr`.
pub open spec fn answered(ws: Set<(ChanId, nat, HMsg)>, k: int, r: int,
                          tr: u64, rid: u64) -> bool {
    exists|i: nat, v: u64, cv: u64| ws.contains((sch(k, r), i, HMsg::Value(tr, v, rid, cv)))
}

/// A PROPAGATION COMPLETED: a quorum acknowledged it.
pub open spec fn propagated(ws: Set<(ChanId, nat, HMsg)>, k: int,
                            t: u64, rid: u64, hi: u64) -> bool {
    exists|q: Set<int>| is_quorum(q) && forall|r: int| q.contains(r) ==> backed(ws, k, r, t, rid, hi)
}

/// A completed write is a completed propagation.
pub open spec fn rec_wdone_prop(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_clog(c) && m is WDone
            ==> propagated(ws, c.ix[0], m->WDone_0, rnd(m), clk(m))
}

/// A RETURN NEEDS BOTH PHASES: a quorum answered the read with tags at most the
/// one returned, and the returned tag was then propagated to a quorum. The
/// second half is the write-back, and it is what stops the next reader from
/// seeing anything older.
pub open spec fn rec_return_phases(ws: Set<(ChanId, nat, HMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: HMsg|
        (#[trigger] ws.contains((c, i, m))) && is_clog(c) && m is Return
            ==> (exists|q: Set<int>| is_quorum(q)
                    && forall|r: int| q.contains(r)
                            ==> exists|tr: u64| tr <= m->Return_0
                                    && answered(ws, c.ix[0], r, tr, rnd(m)))
                && propagated(ws, c.ix[0], m->Return_0, rnd(m), clk(m))
}

impl NetInv<HMsg> for AbdHb {
    /// Every log's clocks strictly increase. That single clause is the whole of
    /// happens-before within a participant.
    open spec fn gate(c: ChanId, s: Seq<HMsg>, m: HMsg) -> bool {
        &&& (is_log(c) ==> forall|x: int| 0 <= x < s.len() ==> clk(#[trigger] s[x]) < clk(m))
        &&& (is_clog(c) ==> m is WDone || m is RStart || m is Return)
        &&& (is_rlog(c) ==> {
                &&& (m is Store || m is Got || m is Rep)
                // A replica never goes backwards. NOT strict: a propagation
                // that does not raise the tag still logs where the replica
                // stands, which is what makes an acknowledgement mean
                // something.
                &&& (m is Store ==> forall|x: int| 0 <= x < s.len() && (#[trigger] s[x]) is Store
                        ==> s[x]->Store_0 <= m->Store_0)
                // ... and never under-reports what it holds.
                &&& (m is Rep ==> forall|x: int| 0 <= x < s.len() && (#[trigger] s[x]) is Store
                        ==> s[x]->Store_0 <= m->Rep_0)
            })
        &&& (is_qch(c) ==> m is Read)
        &&& (is_sch(c) ==> m is Value)
        &&& (is_bch(c) ==> m is Prop)
        &&& (is_bach(c) ==> m is BAck)
    }

    open spec fn wit_inv(c: ChanId, m: HMsg) -> bool {
        &&& (forall|k: int, r: int| c == #[trigger] qch(k, r) ==> m is Read)
        &&& (forall|k: int, r: int| c == #[trigger] sch(k, r) ==> m is Value)
        &&& (forall|k: int, r: int| c == #[trigger] bch(k, r) ==> m is Prop)
        &&& (forall|k: int, r: int| c == #[trigger] bach(k, r) ==> m is BAck)
    }

    open spec fn deliverable_at(v: Seq<HMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn history_inv(sent: Map<ChanId, Seq<HMsg>>) -> bool { true }
    open spec fn pair_gives(c: ChanId, m1: HMsg, m2: HMsg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<HMsg>>, c: ChanId,
                              i: nat, j: nat, m1: HMsg, m2: HMsg) { }
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<HMsg>, m: HMsg) {
        assert forall|k: int, r: int| c == #[trigger] qch(k, r) implies m is Read by {
            assert(seq![k, r, 0][0] == k); assert(seq![k, r, 0][1] == r);
        }
        assert forall|k: int, r: int| c == #[trigger] sch(k, r) implies m is Value by {
            assert(seq![k, r, 0][0] == k); assert(seq![k, r, 0][1] == r);
        }
        assert forall|k: int, r: int| c == #[trigger] bch(k, r) implies m is Prop by {
            assert(seq![k, r, 0][0] == k); assert(seq![k, r, 0][1] == r);
        }
        assert forall|k: int, r: int| c == #[trigger] bach(k, r) implies m is BAck by {
            assert(seq![k, r, 0][0] == k); assert(seq![k, r, 0][1] == r);
        }
    }
    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<HMsg>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<HMsg>>,
                                         was_sent: Set<(ChanId, nat, HMsg)>,
                                         c: ChanId, s: Seq<HMsg>, m: HMsg,
                                         causes: Set<(ChanId, nat, HMsg)>) { }

    open spec fn needs_cause(c: ChanId, m: HMsg) -> bool {
        ||| is_bach(c)
        ||| is_qch(c)
        ||| is_sch(c)
        ||| (is_rlog(c) && m is Got)
        ||| (is_rlog(c) && m is Rep)
        ||| (is_clog(c) && (m is WDone || m is Return))
    }

    open spec fn caused_by(c: ChanId, m: HMsg, causes: Set<(ChanId, nat, HMsg)>) -> bool {
        &&& (is_bach(c) ==> exists|j: nat, ms: HMsg| causes.contains((rlog(c.ix[1]), j, ms))
                && ms is Store && m->BAck_0 <= ms->Store_0 && clk(ms) < clk(m))
        &&& (is_qch(c) ==> exists|j: nat, mr: HMsg| causes.contains((clog(c.ix[0]), j, mr))
                && mr is RStart && clk(mr) == rnd(m) && clk(mr) < clk(m))
        &&& (is_sch(c) ==> exists|j: nat, mp: HMsg| causes.contains((rlog(c.ix[1]), j, mp))
                && mp is Rep && mp->Rep_0 == m->Value_0
                && rnd(mp) == rnd(m) && clk(mp) < clk(m))
        &&& (is_rlog(c) && m is Got ==> exists|k: int, j: nat, mq: HMsg|
                causes.contains((qch(k, c.ix[0]), j, mq))
                && mq is Read && rnd(mq) == rnd(m) && clk(mq) < clk(m))
        &&& (is_rlog(c) && m is Rep ==> exists|j: nat, mg: HMsg| causes.contains((c, j, mg))
                && mg is Got && rnd(mg) == rnd(m) && clk(mg) < clk(m))
        &&& (is_clog(c) && m is WDone
                ==> propagated(causes, c.ix[0], m->WDone_0, rnd(m), clk(m)))
        &&& (is_clog(c) && m is Return ==> {
                &&& exists|q: Set<int>| is_quorum(q)
                        && forall|r: int| q.contains(r)
                                ==> exists|tr: u64| tr <= m->Return_0
                                        && answered(causes, c.ix[0], r, tr, rnd(m))
                &&& propagated(causes, c.ix[0], m->Return_0, rnd(m), clk(m))
            })
    }

    open spec fn caused_by1(c: ChanId, m: HMsg, d: ChanId, j: nat, m2: HMsg) -> bool {
        &&& (is_bach(c) ==> d == rlog(c.ix[1]) && m2 is Store
                && m->BAck_0 <= m2->Store_0 && clk(m2) < clk(m))
        &&& (is_qch(c) ==> d == clog(c.ix[0]) && m2 is RStart
                && clk(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_sch(c) ==> d == rlog(c.ix[1]) && m2 is Rep && m2->Rep_0 == m->Value_0
                && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_rlog(c) && m is Got ==> d == qch(d.ix[0], c.ix[0]) && m2 is Read
                && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& (is_rlog(c) && m is Rep ==> d == c && m2 is Got
                && rnd(m2) == rnd(m) && clk(m2) < clk(m))
        &&& !(is_clog(c) && (m is WDone || m is Return))
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
        &&& rec_back_after_store(ws)
        &&& rec_got_after_read(ws)
        &&& rec_read_after_rstart(ws)
        &&& rec_rep_after_got(ws)
        &&& rec_value_after_rep(ws)
        &&& rec_wdone_prop(ws)
        &&& rec_return_phases(ws)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, HMsg)>,
                                        sent: Map<ChanId, Seq<HMsg>>,
                                        c: ChanId, s: Seq<HMsg>, m: HMsg,
                                        causes: Set<(ChanId, nat, HMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

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
            (#[trigger] post.contains((k, x, mm))) && is_bach(k)
            implies exists|j: nat, ms: HMsg| post.contains((rlog(k.ix[1]), j, ms))
                && ms is Store && mm->BAck_0 <= ms->Store_0 && clk(ms) < clk(mm) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            let (j0, ms0) = choose|j: nat, ms: HMsg| src.contains((rlog(k.ix[1]), j, ms))
                && ms is Store && mm->BAck_0 <= ms->Store_0 && clk(ms) < clk(mm);
            assert(post.contains((rlog(k.ix[1]), j0, ms0)));
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rlog(k) && mm is Got
            implies exists|kk: int, j: nat, mq: HMsg| post.contains((qch(kk, k.ix[0]), j, mq))
                && mq is Read && rnd(mq) == rnd(mm) && clk(mq) < clk(mm) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            let (k0, j0, mq0) = choose|kk: int, j: nat, mq: HMsg|
                src.contains((qch(kk, k.ix[0]), j, mq))
                && mq is Read && rnd(mq) == rnd(mm) && clk(mq) < clk(mm);
            assert(post.contains((qch(k0, k.ix[0]), j0, mq0)));
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_qch(k)
            implies exists|j: nat, mr: HMsg| post.contains((clog(k.ix[0]), j, mr))
                && mr is RStart && clk(mr) == rnd(mm) && clk(mr) < clk(mm) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            let (j0, mr0) = choose|j: nat, mr: HMsg| src.contains((clog(k.ix[0]), j, mr))
                && mr is RStart && clk(mr) == rnd(mm) && clk(mr) < clk(mm);
            assert(post.contains((clog(k.ix[0]), j0, mr0)));
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rlog(k) && mm is Rep
            implies exists|j: nat, mg: HMsg| post.contains((k, j, mg))
                && mg is Got && rnd(mg) == rnd(mm) && clk(mg) < clk(mm) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            let (j0, mg0) = choose|j: nat, mg: HMsg| src.contains((k, j, mg))
                && mg is Got && rnd(mg) == rnd(mm) && clk(mg) < clk(mm);
            assert(post.contains((k, j0, mg0)));
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_sch(k)
            implies exists|j: nat, mp: HMsg| post.contains((rlog(k.ix[1]), j, mp))
                && mp is Rep && mp->Rep_0 == mm->Value_0
                && rnd(mp) == rnd(mm) && clk(mp) < clk(mm) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            let (j0, mp0) = choose|j: nat, mp: HMsg| src.contains((rlog(k.ix[1]), j, mp))
                && mp is Rep && mp->Rep_0 == mm->Value_0
                && rnd(mp) == rnd(mm) && clk(mp) < clk(mm);
            assert(post.contains((rlog(k.ix[1]), j0, mp0)));
        }

        // ---- the quorum edges ----
        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_clog(k) && mm is WDone
            implies propagated(post, k.ix[0], mm->WDone_0, rnd(mm), clk(mm)) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            lemma_propagated_mono(src, post, k.ix[0], mm->WDone_0, rnd(mm), clk(mm));
        }

        assert forall|k: ChanId, x: nat, mm: HMsg|
            (#[trigger] post.contains((k, x, mm))) && is_clog(k) && mm is Return
            implies (exists|q: Set<int>| is_quorum(q)
                        && forall|r: int| q.contains(r)
                                ==> exists|tr: u64| tr <= mm->Return_0
                                        && answered(post, k.ix[0], r, tr, rnd(mm)))
                    && propagated(post, k.ix[0], mm->Return_0, rnd(mm), clk(mm)) by {
            let src = if (k, x, mm) == e { causes } else { was_sent };
            lemma_propagated_mono(src, post, k.ix[0], mm->Return_0, rnd(mm), clk(mm));
            let q0 = choose|q: Set<int>| is_quorum(q)
                && forall|r: int| q.contains(r)
                        ==> exists|tr: u64| tr <= mm->Return_0
                                && answered(src, k.ix[0], r, tr, rnd(mm));
            assert forall|r: int| q0.contains(r) implies
                exists|tr: u64| tr <= mm->Return_0
                    && answered(post, k.ix[0], r, tr, rnd(mm)) by {
                let t0 = choose|tr: u64| tr <= mm->Return_0
                    && answered(src, k.ix[0], r, tr, rnd(mm));
                let (vi, vv, cv) = choose|vi: nat, vv: u64, cv: u64|
                    src.contains((sch(k.ix[0], r), vi, HMsg::Value(t0, vv, rnd(mm), cv)));
                assert(post.contains((sch(k.ix[0], r), vi, HMsg::Value(t0, vv, rnd(mm), cv))));
                assert(answered(post, k.ix[0], r, t0, rnd(mm)));
            }
        }
    }
}

impl DetDelivery<HMsg> for AbdHb {
    proof fn lemma_delivery_determined(v: Seq<HMsg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}

/// A completed propagation survives the record growing.
pub proof fn lemma_propagated_mono(
    ws1: Set<(ChanId, nat, HMsg)>, ws2: Set<(ChanId, nat, HMsg)>,
    k: int, t: u64, rid: u64, hi: u64,
)
    requires propagated(ws1, k, t, rid, hi), ws1.subset_of(ws2),
    ensures  propagated(ws2, k, t, rid, hi),
{
    let q = choose|q: Set<int>| is_quorum(q)
        && forall|r: int| q.contains(r) ==> backed(ws1, k, r, t, rid, hi);
    assert forall|r: int| q.contains(r) implies backed(ws2, k, r, t, rid, hi) by {
        let (i, cb) = choose|i: nat, cb: u64|
            ws1.contains((bach(k, r), i, HMsg::BAck(t, rid, cb))) && cb < hi;
        assert(ws2.contains((bach(k, r), i, HMsg::BAck(t, rid, cb))));
    }
}


// ---------------------------------------------------------------------------
// Happens-before, as two lemmas
// ---------------------------------------------------------------------------

/// COMPARING CLOCKS DECIDES ORDER WITHIN A LOG.
///
/// A bigger clock means a later position. This is the contrapositive of the
/// gate, and it is what turns a chain of provenance into a statement about one
/// participant's own history.
pub proof fn lemma_clock_gives_position(
    ws: Set<(ChanId, nat, HMsg)>, c: ChanId, i: nat, j: nat, m1: HMsg, m2: HMsg,
)
    requires
        rec_clock_order(ws), rec_functional(ws), is_log(c),
        ws.contains((c, i, m1)), ws.contains((c, j, m2)),
        clk(m1) < clk(m2),
    ensures i < j,
{
    if j < i { assert(clk(m2) < clk(m1)); }
    if i == j { assert(m1 == m2); }
}

/// A REPLICA THAT LOGGED `t` BEFORE IT ANSWERED, ANSWERS AT LEAST `t`.
pub proof fn lemma_replica_reports_high(
    ws: Set<(ChanId, nat, HMsg)>, r: int, i: nat, k: nat, ms: HMsg, mp: HMsg,
)
    requires
        rec_clock_order(ws), rec_functional(ws), rec_rep_dominates(ws),
        ws.contains((rlog(r), i, ms)), ms is Store,
        ws.contains((rlog(r), k, mp)), mp is Rep,
        clk(ms) < clk(mp),
    ensures ms->Store_0 <= mp->Rep_0,
{
    lemma_shapes(0, r);
    lemma_clock_gives_position(ws, rlog(r), i, k, ms, mp);
}

/// THE STEP BOTH THEOREMS SHARE.
///
/// If a propagation of `t` finished before round `rid` began, then every reply
/// in that round reports at least `t` -- so a read in that round returns at
/// least `t`. The quorums intersect, and at the replica in both, the clock
/// chain puts the store before the reply.
pub proof fn lemma_propagation_is_seen(
    ws: Set<(ChanId, nat, HMsg)>,
    k1: int, t: u64, rid1: u64, hi: u64,
    k2: int, i2: nat, m2: HMsg,
)
    requires
        AbdHb::record_inv(ws),
        propagated(ws, k1, t, rid1, hi),
        ws.contains((clog(k2), i2, m2)), m2 is Return,
        // the propagation finished before this round started
        hi <= rnd(m2),
    ensures
        t <= m2->Return_0,
{
    lemma_shapes(k2, 0);
    let rid2 = rnd(m2);

    // The propagating quorum, and the quorum that answered the read.
    let qb = choose|q: Set<int>| is_quorum(q)
        && forall|r: int| q.contains(r) ==> backed(ws, k1, r, t, rid1, hi);
    let q2 = choose|q: Set<int>| is_quorum(q)
        && forall|r: int| q.contains(r)
                ==> exists|tr: u64| tr <= m2->Return_0 && answered(ws, k2, r, tr, rid2);
    lemma_quorum_intersect(qb, q2);
    let r = choose|r: int| qb.contains(r) && q2.contains(r);
    lemma_shapes(k1, r);
    lemma_shapes(k2, r);

    // At `r`: the acknowledgement, and the store behind it.
    let (bi, cb) = choose|bi: nat, cb: u64|
        ws.contains((bach(k1, r), bi, HMsg::BAck(t, rid1, cb))) && cb < hi;
    let (si, ms) = choose|si: nat, ms: HMsg| ws.contains((rlog(r), si, ms))
        && ms is Store && t <= ms->Store_0 && clk(ms) < cb;

    // At `r`: the reply to round `rid2`, and the chain back to the round start.
    let x = choose|tr: u64| tr <= m2->Return_0 && answered(ws, k2, r, tr, rid2);
    let (vi, vv, cv) = choose|vi: nat, vv: u64, cv: u64|
        ws.contains((sch(k2, r), vi, HMsg::Value(x, vv, rid2, cv)));
    let (pi, mp) = choose|pi: nat, mp: HMsg| ws.contains((rlog(r), pi, mp))
        && mp is Rep && mp->Rep_0 == x && rnd(mp) == rid2 && clk(mp) < cv;
    let (gi, mg) = choose|gi: nat, mg: HMsg| ws.contains((rlog(r), gi, mg))
        && mg is Got && rnd(mg) == rid2 && clk(mg) < clk(mp);
    let (kq, qi, mq) = choose|kq: int, qi: nat, mq: HMsg|
        ws.contains((qch(kq, r), qi, mq))
        && mq is Read && rnd(mq) == rid2 && clk(mq) < clk(mg);
    lemma_shapes(kq, r);
    let (ri, mr) = choose|ri: nat, mr: HMsg| ws.contains((clog(kq), ri, mr))
        && mr is RStart && clk(mr) == rid2 && clk(mr) < clk(mq);

    // store < ack < propagation done <= round start < read < got < reply
    assert(clk(ms) < cb && cb < hi && hi <= rid2 && rid2 == clk(mr));
    assert(clk(mr) < clk(mq) && clk(mq) < clk(mg) && clk(mg) < clk(mp));

    lemma_replica_reports_high(ws, r, si, pi, ms, mp);
}

/// ATOMICITY, PART ONE: a read that began after a write completed returns at
/// least that write's tag.
pub proof fn lemma_read_sees_write(
    ws: Set<(ChanId, nat, HMsg)>,
    k1: int, i1: nat, m1: HMsg,
    k2: int, i2: nat, m2: HMsg,
)
    requires
        AbdHb::record_inv(ws),
        ws.contains((clog(k1), i1, m1)), m1 is WDone,
        ws.contains((clog(k2), i2, m2)), m2 is Return,
        clk(m1) <= rnd(m2),
    ensures
        m1->WDone_0 <= m2->Return_0,
{
    lemma_shapes(k1, 0);
    lemma_propagation_is_seen(ws, k1, m1->WDone_0, rnd(m1), clk(m1), k2, i2, m2);
}

/// ATOMICITY, PART TWO: NO NEW-OLD INVERSION.
///
/// A read that began after another read returned cannot return an older tag.
/// This is what the write-back is for, and it is the clause that distinguishes
/// an atomic register from a merely regular one: the first reader propagated
/// what it was about to return, so the second reader's quorum cannot have
/// missed it.
pub proof fn lemma_no_inversion(
    ws: Set<(ChanId, nat, HMsg)>,
    k1: int, i1: nat, m1: HMsg,
    k2: int, i2: nat, m2: HMsg,
)
    requires
        AbdHb::record_inv(ws),
        ws.contains((clog(k1), i1, m1)), m1 is Return,
        ws.contains((clog(k2), i2, m2)), m2 is Return,
        // the second read began after the first one returned
        clk(m1) <= rnd(m2),
    ensures
        m1->Return_0 <= m2->Return_0,
{
    lemma_shapes(k1, 0);
    lemma_propagation_is_seen(ws, k1, m1->Return_0, rnd(m1), clk(m1), k2, i2, m2);
}


/// NOT VACUOUS: the chain has a start.
///
/// Two sends need no justification -- a replica may log a store, and a client
/// may begin a read -- and an empty log accepts any clock, so the chain can
/// begin and every later link has something to point at. `spike/crosschan.rs`
/// was once vacuous for want of exactly this check.
pub proof fn lemma_protocol_enabled()
    ensures
        !AbdHb::needs_cause(rlog(0), HMsg::Store(1, 7, 1)),
        !AbdHb::needs_cause(clog(0), HMsg::RStart(1)),
        AbdHb::gate(rlog(0), Seq::<HMsg>::empty(), HMsg::Store(1, 7, 1)),
        AbdHb::gate(clog(0), Seq::<HMsg>::empty(), HMsg::RStart(1)),
{
    lemma_shapes(0, 0);
    assert(rlog(0) != clog(0)) by { lemma_chan_distinct(1, seq![0int], 0, seq![0int]); }
}

} // verus!
