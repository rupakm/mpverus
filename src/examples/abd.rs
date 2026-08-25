// ABD: a single-writer multi-reader register replicated across n nodes.
//
// The writer tags each value with a strictly increasing sequence number and
// sends it to every replica; a replica stores a tag only if it exceeds what it
// holds, and acknowledges. A reader asks every replica, takes the highest tag
// it hears from a quorum, writes that back to a quorum, and returns the value.
//
// WHAT THIS FILE PROVES: every value a reader can return was really written by
// the writer under that tag, and the tag determines the value. That is a chain
// of provenance across four channels -- return, reply, store, write -- ending
// at the writer's own log, and each link is a `caused_by1` obligation on one
// send.
//
// WHAT IT DOES NOT PROVE, and this is the point of building it: ATOMICITY. See
// the note at the end. The survey in `docs/plan.md` was optimistic about this
// protocol, and building it is what showed why.
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::tok::*;
use crate::proc::*;

verus! {

// ---------------------------------------------------------------------------
// Channels and messages
// ---------------------------------------------------------------------------

/// The writer's own log: every value it ever wrote, in order. One channel it
/// alone writes, so "the tag determines the value" is a condition on one
/// history and a gate can enforce it.
pub open spec fn wlog() -> ChanId { chan(0, seq![]) }
/// Writer to replica `r`.
pub open spec fn wr(r: int) -> ChanId { chan(1, seq![r]) }
/// Replica `r`'s own log: every value it ever stored, in order.
pub open spec fn rlog(r: int) -> ChanId { chan(2, seq![r]) }
/// Replica `r` to the writer.
pub open spec fn ack(r: int) -> ChanId { chan(3, seq![r]) }
/// Reader to replica `r`, and back.
pub open spec fn rreq(r: int) -> ChanId { chan(4, seq![r]) }
pub open spec fn rrsp(r: int) -> ChanId { chan(5, seq![r]) }
/// The reader's own log: what it returned.
pub open spec fn rdlog() -> ChanId { chan(6, seq![]) }

#[derive(Structural, PartialEq, Eq)]
pub enum AMsg {
    /// The writer's log entry.
    WVal(u64, u64),
    Write(u64, u64),
    /// A replica's log entry.
    Store(u64, u64),
    Ack(u64),
    Read,
    Value(u64, u64),
    /// The reader's log entry.
    Return(u64, u64),
}

/// The tag of a tagged message.
pub open spec fn tag_of(m: AMsg) -> u64 {
    if m is WVal { m->WVal_0 }
    else if m is Write { m->Write_0 }
    else if m is Store { m->Store_0 }
    else if m is Value { m->Value_0 }
    else { m->Return_0 }
}

pub open spec fn is_wr(c: ChanId)   -> bool { c == wr(c.ix[0]) }
pub open spec fn is_rlog(c: ChanId) -> bool { c == rlog(c.ix[0]) }
pub open spec fn is_rrsp(c: ChanId) -> bool { c == rrsp(c.ix[0]) }

pub proof fn lemma_shapes(r: int)
    ensures
        is_wr(wr(r)), wr(r).ix[0] == r,
        is_rlog(rlog(r)), rlog(r).ix[0] == r,
        is_rrsp(rrsp(r)), rrsp(r).ix[0] == r,
{
    assert(seq![r][0] == r);
}

/// A history of tagged entries whose tags strictly increase.
pub open spec fn tags_increase(h: Seq<AMsg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len() ==> tag_of(#[trigger] h[x]) < tag_of(#[trigger] h[y])
}

pub struct Abd;

// ---------------------------------------------------------------------------
// The record invariant: a chain of provenance, ending at the writer's log
// ---------------------------------------------------------------------------

/// The writer's log binds a tag to one value. It holds because the gate makes
/// tags strictly increasing, so no tag occurs twice.
pub open spec fn rec_wtag_unique(ws: Set<(ChanId, nat, AMsg)>) -> bool {
    forall|i: nat, j: nat, t: u64, v1: u64, v2: u64|
        (#[trigger] ws.contains((wlog(), i, AMsg::WVal(t, v1))))
        && (#[trigger] ws.contains((wlog(), j, AMsg::WVal(t, v2))))
            ==> v1 == v2
}

/// Every value sent to a replica is one the writer really wrote.
pub open spec fn rec_write_backed(ws: Set<(ChanId, nat, AMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: AMsg|
        (#[trigger] ws.contains((c, i, m))) && is_wr(c)
            ==> exists|j: nat| ws.contains((wlog(), j, AMsg::WVal(m->Write_0, m->Write_1)))
}

/// Every value a replica stores is one the writer sent it.
pub open spec fn rec_store_backed(ws: Set<(ChanId, nat, AMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: AMsg|
        (#[trigger] ws.contains((c, i, m))) && is_rlog(c)
            ==> exists|j: nat| ws.contains(
                    (wr(c.ix[0]), j, AMsg::Write(m->Store_0, m->Store_1)))
}

/// Every value a replica reports is one it stored.
pub open spec fn rec_value_backed(ws: Set<(ChanId, nat, AMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: AMsg|
        (#[trigger] ws.contains((c, i, m))) && is_rrsp(c)
            ==> exists|j: nat| ws.contains(
                    (rlog(c.ix[0]), j, AMsg::Store(m->Value_0, m->Value_1)))
}

/// Every value a reader returns is one some replica reported.
pub open spec fn rec_return_backed(ws: Set<(ChanId, nat, AMsg)>) -> bool {
    forall|i: nat, m: AMsg|
        (#[trigger] ws.contains((rdlog(), i, m)))
            ==> exists|r: int, j: nat| ws.contains(
                    (rrsp(r), j, AMsg::Value(m->Return_0, m->Return_1)))
}

impl NetInv<AMsg> for Abd {
    /// Two logs are gated, and both say the same thing: tags strictly increase.
    /// On the writer's log that makes the tag a key; on a replica's log it is
    /// the rule that a replica never goes backwards.
    open spec fn gate(c: ChanId, s: Seq<AMsg>, m: AMsg) -> bool {
        &&& (c == wlog() ==> m is WVal
                && forall|x: int| 0 <= x < s.len() ==> tag_of(#[trigger] s[x]) < tag_of(m))
        &&& (is_rlog(c) ==> m is Store
                && forall|x: int| 0 <= x < s.len() ==> tag_of(#[trigger] s[x]) < tag_of(m))
        &&& (is_wr(c) ==> m is Write)
        &&& (is_rrsp(c) ==> m is Value)
        &&& (c == rdlog() ==> m is Return)
    }

    open spec fn wit_inv(c: ChanId, m: AMsg) -> bool {
        &&& (c == wlog() ==> m is WVal)
        &&& (forall|r: int| c == #[trigger] rlog(r) ==> m is Store)
        &&& (forall|r: int| c == #[trigger] wr(r) ==> m is Write)
        &&& (forall|r: int| c == #[trigger] rrsp(r) ==> m is Value)
        &&& (c == rdlog() ==> m is Return)
    }

    open spec fn deliverable_at(v: Seq<AMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn history_inv(sent: Map<ChanId, Seq<AMsg>>) -> bool { true }
    open spec fn pair_gives(c: ChanId, m1: AMsg, m2: AMsg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<AMsg>>, c: ChanId,
                              i: nat, j: nat, m1: AMsg, m2: AMsg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<AMsg>, m: AMsg) {
        assert forall|r: int| c == #[trigger] rlog(r) implies m is Store by {
            assert(seq![r][0] == r);
        }
        assert forall|r: int| c == #[trigger] wr(r) implies m is Write by {
            assert(seq![r][0] == r);
        }
        assert forall|r: int| c == #[trigger] rrsp(r) implies m is Value by {
            assert(seq![r][0] == r);
        }
    }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<AMsg>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<AMsg>>,
                                         was_sent: Set<(ChanId, nat, AMsg)>,
                                         c: ChanId, s: Seq<AMsg>, m: AMsg,
                                         causes: Set<(ChanId, nat, AMsg)>) { }

    /// Every link of the chain is one message pointing at one earlier message,
    /// so every obligation here is single-cause. ABD needs no set-valued
    /// justification for the part that is provable.
    open spec fn needs_cause(c: ChanId, m: AMsg) -> bool {
        is_wr(c) || is_rlog(c) || is_rrsp(c) || c == rdlog()
    }

    open spec fn caused_by(c: ChanId, m: AMsg, causes: Set<(ChanId, nat, AMsg)>) -> bool {
        &&& (is_wr(c) ==> exists|j: nat| causes.contains(
                (wlog(), j, AMsg::WVal(m->Write_0, m->Write_1))))
        &&& (is_rlog(c) ==> exists|j: nat| causes.contains(
                (wr(c.ix[0]), j, AMsg::Write(m->Store_0, m->Store_1))))
        &&& (is_rrsp(c) ==> exists|j: nat| causes.contains(
                (rlog(c.ix[0]), j, AMsg::Store(m->Value_0, m->Value_1))))
        &&& (c == rdlog() ==> exists|r: int, j: nat| causes.contains(
                (rrsp(r), j, AMsg::Value(m->Return_0, m->Return_1))))
    }

    open spec fn caused_by1(c: ChanId, m: AMsg, d: ChanId, j: nat, m2: AMsg) -> bool {
        &&& (is_wr(c) ==> d == wlog() && m2 == AMsg::WVal(m->Write_0, m->Write_1))
        &&& (is_rlog(c) ==> d == wr(c.ix[0]) && m2 == AMsg::Write(m->Store_0, m->Store_1))
        &&& (is_rrsp(c) ==> d == rlog(c.ix[0]) && m2 == AMsg::Store(m->Value_0, m->Value_1))
        &&& (c == rdlog() ==> d == rrsp(d.ix[0])
                && m2 == AMsg::Value(m->Return_0, m->Return_1))
    }

    proof fn lemma_caused_by1(c: ChanId, m: AMsg, d: ChanId, j: nat, m2: AMsg) {
        let cs = set![(d, j, m2)];
        if is_wr(c) {
            assert(cs.contains((wlog(), j, AMsg::WVal(m->Write_0, m->Write_1))));
        }
        if is_rlog(c) {
            assert(cs.contains((wr(c.ix[0]), j, AMsg::Write(m->Store_0, m->Store_1))));
        }
        if is_rrsp(c) {
            assert(cs.contains((rlog(c.ix[0]), j, AMsg::Store(m->Value_0, m->Value_1))));
        }
        if c == rdlog() {
            assert(cs.contains((rrsp(d.ix[0]), j, AMsg::Value(m->Return_0, m->Return_1))));
        }
    }

    open spec fn caused_by2(c: ChanId, m: AMsg, d1: ChanId, j1: nat, m1: AMsg,
                            d2: ChanId, j2: nat, m2: AMsg) -> bool { false }
    proof fn lemma_caused_by2(c: ChanId, m: AMsg, d1: ChanId, j1: nat, m1: AMsg,
                              d2: ChanId, j2: nat, m2: AMsg) { }

    open spec fn cause_gives(c: ChanId, m: AMsg) -> bool { true }
    proof fn lemma_cause_gives(c: ChanId, m: AMsg, causes: Set<(ChanId, nat, AMsg)>) { }

    open spec fn record_inv(ws: Set<(ChanId, nat, AMsg)>) -> bool {
        &&& rec_wtag_unique(ws)
        &&& rec_write_backed(ws)
        &&& rec_store_backed(ws)
        &&& rec_value_backed(ws)
        &&& rec_return_backed(ws)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, AMsg)>,
                                        sent: Map<ChanId, Seq<AMsg>>,
                                        c: ChanId, s: Seq<AMsg>, m: AMsg,
                                        causes: Set<(ChanId, nat, AMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

        // ---- the writer's log still binds a tag to one value ----
        // The gate says the new tag exceeds every tag already in the history,
        // and every recorded entry IS at a position of that history.
        assert forall|i: nat, j: nat, t: u64, v1: u64, v2: u64|
            (#[trigger] post.contains((wlog(), i, AMsg::WVal(t, v1))))
            && (#[trigger] post.contains((wlog(), j, AMsg::WVal(t, v2))))
            implies v1 == v2 by {
            if (wlog(), i, AMsg::WVal(t, v1)) == e && (wlog(), j, AMsg::WVal(t, v2)) != e {
                assert(was_sent.contains((wlog(), j, AMsg::WVal(t, v2))));
                assert(j < sent[wlog()].len() && sent[wlog()][j as int] == AMsg::WVal(t, v2));
                assert(tag_of(s[j as int]) < tag_of(m));
            }
            if (wlog(), j, AMsg::WVal(t, v2)) == e && (wlog(), i, AMsg::WVal(t, v1)) != e {
                assert(was_sent.contains((wlog(), i, AMsg::WVal(t, v1))));
                assert(i < sent[wlog()].len() && sent[wlog()][i as int] == AMsg::WVal(t, v1));
                assert(tag_of(s[i as int]) < tag_of(m));
            }
        }

        // ---- each link of the chain ----
        assert forall|k: ChanId, x: nat, mm: AMsg|
            (#[trigger] post.contains((k, x, mm))) && is_wr(k)
            implies exists|j: nat| post.contains(
                (wlog(), j, AMsg::WVal(mm->Write_0, mm->Write_1))) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let j0 = choose|j: nat| causes.contains(
                    (wlog(), j, AMsg::WVal(m->Write_0, m->Write_1)));
                assert(post.contains((wlog(), j0, AMsg::WVal(mm->Write_0, mm->Write_1))));
            } else {
                lemma_wit_mono(was_sent, e, wlog(), AMsg::WVal(mm->Write_0, mm->Write_1));
            }
        }
        assert forall|k: ChanId, x: nat, mm: AMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rlog(k)
            implies exists|j: nat| post.contains(
                (wr(k.ix[0]), j, AMsg::Write(mm->Store_0, mm->Store_1))) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let j0 = choose|j: nat| causes.contains(
                    (wr(c.ix[0]), j, AMsg::Write(m->Store_0, m->Store_1)));
                assert(post.contains((wr(k.ix[0]), j0, AMsg::Write(mm->Store_0, mm->Store_1))));
            } else {
                lemma_wit_mono(was_sent, e, wr(k.ix[0]), AMsg::Write(mm->Store_0, mm->Store_1));
            }
        }
        assert forall|k: ChanId, x: nat, mm: AMsg|
            (#[trigger] post.contains((k, x, mm))) && is_rrsp(k)
            implies exists|j: nat| post.contains(
                (rlog(k.ix[0]), j, AMsg::Store(mm->Value_0, mm->Value_1))) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let j0 = choose|j: nat| causes.contains(
                    (rlog(c.ix[0]), j, AMsg::Store(m->Value_0, m->Value_1)));
                assert(post.contains((rlog(k.ix[0]), j0, AMsg::Store(mm->Value_0, mm->Value_1))));
            } else {
                lemma_wit_mono(was_sent, e, rlog(k.ix[0]), AMsg::Store(mm->Value_0, mm->Value_1));
            }
        }
        assert forall|x: nat, mm: AMsg|
            (#[trigger] post.contains((rdlog(), x, mm)))
            implies exists|r: int, j: nat| post.contains(
                (rrsp(r), j, AMsg::Value(mm->Return_0, mm->Return_1))) by {
            if (rdlog(), x, mm) == e {
                assert(Self::needs_cause(c, m));
                let (r0, j0) = choose|r: int, j: nat| causes.contains(
                    (rrsp(r), j, AMsg::Value(m->Return_0, m->Return_1)));
                assert(post.contains((rrsp(r0), j0, AMsg::Value(mm->Return_0, mm->Return_1))));
            } else {
                let (r0, j0) = choose|r: int, j: nat| was_sent.contains(
                    (rrsp(r), j, AMsg::Value(mm->Return_0, mm->Return_1)));
                assert(post.contains((rrsp(r0), j0, AMsg::Value(mm->Return_0, mm->Return_1))));
            }
        }
    }
}

impl DetDelivery<AMsg> for Abd {
    proof fn lemma_delivery_determined(v: Seq<AMsg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}

/// A witness already in the record survives one more entry.
pub proof fn lemma_wit_mono(
    ws: Set<(ChanId, nat, AMsg)>, e: (ChanId, nat, AMsg), d: ChanId, m: AMsg,
)
    requires exists|j: nat| ws.contains((d, j, m)),
    ensures  exists|j: nat| ws.insert(e).contains((d, j, m)),
{
    let j0 = choose|j: nat| ws.contains((d, j, m));
    assert(ws.insert(e).contains((d, j0, m)));
}


// ---------------------------------------------------------------------------
// Safety
// ---------------------------------------------------------------------------

/// The reader returned `(t, v)`.
pub open spec fn returned(ws: Set<(ChanId, nat, AMsg)>, t: u64, v: u64) -> bool {
    exists|i: nat| ws.contains((rdlog(), i, AMsg::Return(t, v)))
}

/// The writer wrote `(t, v)`.
pub open spec fn written(ws: Set<(ChanId, nat, AMsg)>, t: u64, v: u64) -> bool {
    exists|i: nat| ws.contains((wlog(), i, AMsg::WVal(t, v)))
}

/// INTEGRITY: every value a reader returns was really written under that tag.
///
/// Four links, each one message pointing at an earlier one: the return points
/// at a replica's reply, the reply at that replica's own store, the store at
/// the write it received, and the write at the writer's log. No gate sees more
/// than one channel; the chain is entirely provenance.
pub proof fn lemma_return_was_written(ws: Set<(ChanId, nat, AMsg)>, t: u64, v: u64)
    requires Abd::record_inv(ws), returned(ws, t, v),
    ensures  written(ws, t, v),
{
    let i = choose|i: nat| ws.contains((rdlog(), i, AMsg::Return(t, v)));
    let (r, j) = choose|r: int, j: nat| ws.contains((rrsp(r), j, AMsg::Value(t, v)));
    lemma_shapes(r);
    let k = choose|k: nat| ws.contains((rlog(r), k, AMsg::Store(t, v)));
    let l = choose|l: nat| ws.contains((wr(r), l, AMsg::Write(t, v)));
    let n = choose|n: nat| ws.contains((wlog(), n, AMsg::WVal(t, v)));
}

/// AND THE TAG DETERMINES THE VALUE. Two reads that return the same tag return
/// the same value, wherever they read it and whichever replicas answered.
pub proof fn lemma_reads_agree(ws: Set<(ChanId, nat, AMsg)>, t: u64, v1: u64, v2: u64)
    requires Abd::record_inv(ws), returned(ws, t, v1), returned(ws, t, v2),
    ensures  v1 == v2,
{
    lemma_return_was_written(ws, t, v1);
    lemma_return_was_written(ws, t, v2);
    let i1 = choose|i: nat| ws.contains((wlog(), i, AMsg::WVal(t, v1)));
    let i2 = choose|i: nat| ws.contains((wlog(), i, AMsg::WVal(t, v2)));
}

// ---------------------------------------------------------------------------
// WHAT IS NOT PROVED HERE, AND WHY
// ---------------------------------------------------------------------------
//
// ATOMICITY. The property ABD exists for is that a read returns the value of
// the most recently completed write, and that reads never go backwards. Neither
// is provable in this framework, and the obstacle is not a missing lemma.
//
// Take the central step. A write COMPLETED with tag `t` means a quorum of
// replicas acknowledged it. A read gathered replies from a quorum. The two
// quorums intersect, at some replica `r`. The argument then needs: `r` had
// already stored `t` when it answered the read. Both events are entries in
// `r`'s own log, so they ARE comparable -- the log is one channel and positions
// are ordered. But which came first depends on when the read happened relative
// to the write, and that is real time. Nothing in a message record says it.
//
// This is the "no global order across channels" limit from `docs/plan.md`,
// reached from an unexpected direction: not from wanting to order two
// participants' events, but from wanting to order one participant's own log
// against another participant's progress.
//
// `pstate` would not settle it either. The missing fact is not a participant's
// current state; it is that one participant's step preceded another's, which no
// invariant over states or messages can express. What would settle it is a
// happens-before relation in the machine -- `pstate` plus a published logical
// clock -- which is the same capability Chandy--Lamport needs.
//
// So ABD splits cleanly, and that is the useful outcome: the provenance half is
// as easy here as anywhere and cost about 300 lines, while the ordering half is
// out of reach by a limit that this protocol makes concrete.

} // verus!
