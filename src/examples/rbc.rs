// RELIABLE BROADCAST, echo-based, crash-tolerant.
//
// One sender broadcasts a value; every process that hears it echoes it to
// everyone; a process DELIVERS the value once a quorum has echoed it.
//
// AGREEMENT: no two processes ever deliver different values. The argument is
// two lines of mathematics and the whole interest is in where each line lives.
//
//   * Two quorums intersect, so some process echoed for both deliveries.
//   * A process echoes at most one value.
//
// The second is the difficulty. A process sends its echoes on one channel per
// destination, so "at most one value" spans n channels and no gate can see it.
// The fix is the pattern Paxos needed: give each process ONE log channel it
// alone writes, gate that channel to accept a single entry, and make every
// outgoing echo carry provenance back to it. The cross-channel property becomes
// a condition on one history, which a gate can enforce.
//
// This is also the only protocol here besides Paxos that justifies a send by a
// SET of causes -- a delivery is backed by a whole quorum of echoes, whose size
// is not known when the trait is written.
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::tok::*;
use crate::proc::*;
use crate::quorum::*;

verus! {

// ---------------------------------------------------------------------------
// Processes and quorums
// ---------------------------------------------------------------------------

pub uninterp spec fn n_proc() -> int;

#[verifier::external_body]
pub proof fn proc_config()
    ensures n_proc() >= 1,
{
}

pub open spec fn procs() -> Set<int> { set_int_range(0, n_proc()) }

pub proof fn lemma_procs()
    ensures
        procs().len() == n_proc(),
        forall|p: int| procs().contains(p) <==> 0 <= p < n_proc(),
{
    proc_config();
    lemma_int_range(0, n_proc());
}

pub open spec fn is_quorum(q: Set<int>) -> bool {
    q.subset_of(procs()) && q.len() + q.len() > n_proc()
}

pub proof fn lemma_quorum_intersect(q1: Set<int>, q2: Set<int>)
    requires is_quorum(q1), is_quorum(q2),
    ensures  exists|p: int| q1.contains(p) && q2.contains(p),
{
    lemma_procs();
    lemma_quorums_intersect(procs(), q1, q2);
}

// ---------------------------------------------------------------------------
// Channels and messages
// ---------------------------------------------------------------------------

/// The broadcaster's channel to process `p`.
pub open spec fn init_ch(p: int) -> ChanId { chan(0, seq![p]) }

/// Process `p`'s ECHO LOG: the one channel it alone writes, and the reason
/// "echoes at most once" is statable at all.
pub open spec fn elog(p: int) -> ChanId { chan(1, seq![p]) }

/// Process `p`'s echo to process `q`. Three indices, because two are reserved
/// for the allocator.
pub open spec fn echo(p: int, q: int) -> ChanId { chan(2, seq![p, q, 0]) }

/// Process `p`'s delivery log: what it decided, before telling anyone.
pub open spec fn dlog(p: int) -> ChanId { chan(3, seq![p]) }

#[derive(Structural, PartialEq, Eq)]
pub enum RMsg {
    Init(u64),
    /// The log entry: "I have committed to echoing this value."
    LEcho(u64),
    Echo(u64),
    Deliver(u64),
}

/// Shape predicates, stated by equality so `wit_inv` can be instantiated.
pub open spec fn is_elog(c: ChanId) -> bool { c == elog(c.ix[0]) }
pub open spec fn is_echo(c: ChanId) -> bool { c == echo(c.ix[0], c.ix[1]) }
pub open spec fn is_dlog(c: ChanId) -> bool { c == dlog(c.ix[0]) }
pub open spec fn is_init(c: ChanId) -> bool { c == init_ch(c.ix[0]) }

pub proof fn lemma_shapes(p: int, q: int)
    ensures
        is_elog(elog(p)), elog(p).ix[0] == p,
        is_dlog(dlog(p)), dlog(p).ix[0] == p,
        is_echo(echo(p, q)), echo(p, q).ix[0] == p, echo(p, q).ix[1] == q,
{
    assert(seq![p][0] == p);
    assert(seq![p, q, 0][0] == p);
    assert(seq![p, q, 0][1] == q);
}

/// Distinct senders have distinct echo channels to the same destination.
pub proof fn lemma_echo_inj(p1: int, p2: int, q: int)
    requires echo(p1, q) == echo(p2, q),
    ensures  p1 == p2,
{
    assert(seq![p1, q, 0][0] == p1);
    assert(seq![p2, q, 0][0] == p2);
}

// ---------------------------------------------------------------------------
// The record invariant
// ---------------------------------------------------------------------------

/// An echo log holds AT MOST ONE entry. Stated as "only position zero is ever
/// written", which is what the gate `s.len() == 0` gives.
pub open spec fn rec_elog_once(ws: Set<(ChanId, nat, RMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: RMsg|
        (#[trigger] ws.contains((c, i, m))) && is_elog(c) ==> i == 0
}

/// Every echo points at its sender's own log entry.
pub open spec fn rec_echo_logged(ws: Set<(ChanId, nat, RMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: RMsg|
        (#[trigger] ws.contains((c, i, m))) && is_echo(c)
            ==> ws.contains((elog(c.ix[0]), 0, PMsgLEcho(m)))
}

/// `LEcho` of an `Echo`'s value, as a function so the clause above has a
/// nameable right-hand side.
pub open spec fn PMsgLEcho(m: RMsg) -> RMsg { RMsg::LEcho(m->Echo_0) }

/// Process `p` echoed `v` to `q`.
pub open spec fn echoed(ws: Set<(ChanId, nat, RMsg)>, p: int, q: int, v: u64) -> bool {
    exists|i: nat| ws.contains((echo(p, q), i, RMsg::Echo(v)))
}

/// A quorum echoed `v` to `q`. This is the obligation a delivery must discharge,
/// and `causes` has the same type as the record, so it is literally the same
/// predicate.
pub open spec fn quorum_echoed(ws: Set<(ChanId, nat, RMsg)>, q: int, v: u64) -> bool {
    exists|s: Set<int>| is_quorum(s) && forall|p: int| s.contains(p) ==> echoed(ws, p, q, v)
}

/// The record is a partial function from (channel, position) to message.
/// A consequence of the machine's own `agree` invariant, restated over the
/// record because that is where this protocol's argument lives.
pub open spec fn rec_functional(ws: Set<(ChanId, nat, RMsg)>) -> bool {
    forall|c: ChanId, i: nat, m1: RMsg, m2: RMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, i, m2)))
            ==> m1 == m2
}

/// Every delivery is backed by a quorum of echoes addressed to the deliverer.
pub open spec fn rec_deliver_backed(ws: Set<(ChanId, nat, RMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: RMsg|
        (#[trigger] ws.contains((c, i, m))) && is_dlog(c) && m is Deliver
            ==> quorum_echoed(ws, c.ix[0], m->Deliver_0)
}

pub struct Rbc;

impl NetInv<RMsg> for Rbc {
    /// Three obligations, each about the one channel being written.
    ///
    /// The echo log takes ONE entry, ever. That single clause is what makes
    /// "a process echoes at most one value" true, and it is checkable because
    /// it mentions only this channel's own history.
    open spec fn gate(c: ChanId, s: Seq<RMsg>, m: RMsg) -> bool {
        &&& (is_elog(c) ==> m is LEcho && s.len() == 0)
        &&& (is_echo(c) ==> m is Echo)
        &&& (is_dlog(c) ==> m is Deliver)
        &&& (is_init(c) ==> m is Init)
    }

    open spec fn wit_inv(c: ChanId, m: RMsg) -> bool {
        &&& (forall|p: int| c == #[trigger] elog(p) ==> m is LEcho)
        &&& (forall|p: int, q: int| c == #[trigger] echo(p, q) ==> m is Echo)
        &&& (forall|p: int| c == #[trigger] dlog(p) ==> m is Deliver)
        &&& (forall|p: int| c == #[trigger] init_ch(p) ==> m is Init)
    }

    open spec fn deliverable_at(v: Seq<RMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    /// Nothing a single history says beyond its gate.
    open spec fn history_inv(sent: Map<ChanId, Seq<RMsg>>) -> bool { true }
    open spec fn pair_gives(c: ChanId, m1: RMsg, m2: RMsg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<RMsg>>, c: ChanId,
                              i: nat, j: nat, m1: RMsg, m2: RMsg) { }
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<RMsg>, m: RMsg) {
        // The gate is stated by shape predicate, the guarantee by equality to a
        // channel name. These are the same thing, but Verus has to be shown the
        // index projection that makes them so.
        assert forall|p: int| c == #[trigger] elog(p) implies m is LEcho by {
            assert(seq![p][0] == p);
        }
        assert forall|p: int| c == #[trigger] dlog(p) implies m is Deliver by {
            assert(seq![p][0] == p);
        }
        assert forall|p: int| c == #[trigger] init_ch(p) implies m is Init by {
            assert(seq![p][0] == p);
        }
        assert forall|p: int, q: int| c == #[trigger] echo(p, q) implies m is Echo by {
            assert(seq![p, q, 0][0] == p);
            assert(seq![p, q, 0][1] == q);
        }
    }
    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<RMsg>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<RMsg>>,
                                         was_sent: Set<(ChanId, nat, RMsg)>,
                                         c: ChanId, s: Seq<RMsg>, m: RMsg,
                                         causes: Set<(ChanId, nat, RMsg)>) { }

    /// Two sends must justify themselves: an echo by its sender's log entry,
    /// and a delivery by a whole quorum of echoes.
    open spec fn needs_cause(c: ChanId, m: RMsg) -> bool {
        is_echo(c) || (is_dlog(c) && m is Deliver)
    }

    open spec fn caused_by(c: ChanId, m: RMsg, causes: Set<(ChanId, nat, RMsg)>) -> bool {
        &&& (is_echo(c) ==> causes.contains((elog(c.ix[0]), 0, RMsg::LEcho(m->Echo_0))))
        // The set-valued case. `causes` has the same type as the record, so the
        // obligation IS the record-level predicate, not a restatement of it.
        &&& (is_dlog(c) && m is Deliver
                ==> quorum_echoed(causes, c.ix[0], m->Deliver_0))
    }

    open spec fn caused_by1(c: ChanId, m: RMsg, d: ChanId, j: nat, m2: RMsg) -> bool {
        &&& (is_echo(c) ==> d == elog(c.ix[0]) && j == 0 && m2 == RMsg::LEcho(m->Echo_0))
        &&& !(is_dlog(c) && m is Deliver)
    }

    proof fn lemma_caused_by1(c: ChanId, m: RMsg, d: ChanId, j: nat, m2: RMsg) {
        let cs = set![(d, j, m2)];
        if is_echo(c) {
            assert(cs.contains((elog(c.ix[0]), 0, RMsg::LEcho(m->Echo_0))));
        }
    }

    open spec fn caused_by2(c: ChanId, m: RMsg, d1: ChanId, j1: nat, m1: RMsg,
                            d2: ChanId, j2: nat, m2: RMsg) -> bool { false }
    proof fn lemma_caused_by2(c: ChanId, m: RMsg, d1: ChanId, j1: nat, m1: RMsg,
                              d2: ChanId, j2: nat, m2: RMsg) { }

    open spec fn cause_gives(c: ChanId, m: RMsg) -> bool { true }
    proof fn lemma_cause_gives(c: ChanId, m: RMsg, causes: Set<(ChanId, nat, RMsg)>) { }

    open spec fn record_inv(was_sent: Set<(ChanId, nat, RMsg)>) -> bool {
        &&& rec_elog_once(was_sent)
        &&& rec_echo_logged(was_sent)
        &&& rec_deliver_backed(was_sent)
        &&& rec_functional(was_sent)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, RMsg)>,
                                        sent: Map<ChanId, Seq<RMsg>>,
                                        c: ChanId, s: Seq<RMsg>, m: RMsg,
                                        causes: Set<(ChanId, nat, RMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

        // ---- the record stays a function ----
        // The new entry is at position `s.len()` of `c`, and every recorded
        // position of `c` is below that, so it cannot collide.
        assert forall|k: ChanId, x: nat, m1: RMsg, m2: RMsg|
            (#[trigger] post.contains((k, x, m1))) && (#[trigger] post.contains((k, x, m2)))
            implies m1 == m2 by {
            if (k, x, m1) == e && (k, x, m2) != e {
                assert(was_sent.contains((k, x, m2)));
                assert(x < sent[k].len());
            }
            if (k, x, m2) == e && (k, x, m1) != e {
                assert(was_sent.contains((k, x, m1)));
                assert(x < sent[k].len());
            }
        }

        // ---- an echo log has only position zero ----
        assert forall|k: ChanId, x: nat, mm: RMsg|
            (#[trigger] post.contains((k, x, mm))) && is_elog(k) implies x == 0 by {
            if (k, x, mm) == e { assert(s.len() == 0); }
        }

        // ---- every echo is backed by its sender's log entry ----
        assert forall|k: ChanId, x: nat, mm: RMsg|
            (#[trigger] post.contains((k, x, mm))) && is_echo(k)
            implies post.contains((elog(k.ix[0]), 0, PMsgLEcho(mm))) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                assert(causes.contains((elog(c.ix[0]), 0, RMsg::LEcho(m->Echo_0))));
            }
        }

        // ---- every delivery still has its quorum ----
        assert forall|k: ChanId, x: nat, mm: RMsg|
            (#[trigger] post.contains((k, x, mm))) && is_dlog(k) && mm is Deliver
            implies quorum_echoed(post, k.ix[0], mm->Deliver_0) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                lemma_quorum_echoed_mono(causes, post, k.ix[0], mm->Deliver_0);
            } else {
                lemma_quorum_echoed_mono(was_sent, post, k.ix[0], mm->Deliver_0);
            }
        }
    }

}

impl DetDelivery<RMsg> for Rbc {
    proof fn lemma_delivery_determined(v: Seq<RMsg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}

/// A quorum of echoes survives the record growing.
pub proof fn lemma_quorum_echoed_mono(
    ws1: Set<(ChanId, nat, RMsg)>, ws2: Set<(ChanId, nat, RMsg)>, q: int, v: u64,
)
    requires quorum_echoed(ws1, q, v), ws1.subset_of(ws2),
    ensures  quorum_echoed(ws2, q, v),
{
    let s = choose|s: Set<int>| is_quorum(s) && forall|p: int| s.contains(p) ==> echoed(ws1, p, q, v);
    assert forall|p: int| s.contains(p) implies echoed(ws2, p, q, v) by {
        let i = choose|i: nat| ws1.contains((echo(p, q), i, RMsg::Echo(v)));
        assert(ws2.contains((echo(p, q), i, RMsg::Echo(v))));
    }
}


/// Quorums exist. Without this, agreement could hold for want of anything ever
/// being delivered.
pub proof fn lemma_all_is_quorum()
    ensures is_quorum(procs()),
{
    lemma_procs();
    proc_config();
}

// ---------------------------------------------------------------------------
// The node, as running code
// ---------------------------------------------------------------------------

/// One participant. It echoes what the broadcaster told it, then delivers once
/// a quorum has echoed the same.
pub struct Node {
    pub id: usize,
    pub n:  usize,
    /// Its own echo log -- the channel that makes "echo once" enforceable.
    pub log:    Out<RMsg, Rbc>,          // elog(id)
    pub echoes: FanOut<RMsg, Rbc>,       // echo(id, q)
    /// Incoming echoes, as a mailbox: a node must not block on a named peer.
    pub inbox:  Inbox<RMsg, Rbc>,        // echo(r, id)
    pub dec:    Out<RMsg, Rbc>,          // dlog(id)
}

impl Node {
    pub open spec fn np(&self) -> nat { self.n as nat }

    pub open spec fn inv(&self) -> bool {
        &&& self.log.wf() && self.log.id() == elog(self.id as int)
        &&& self.dec.wf() && self.dec.id() == dlog(self.id as int)
        &&& self.echoes.wf() && self.inbox.wf()
        &&& self.echoes.len() == self.np() && self.inbox.len() == self.np()
        &&& self.np() == n_proc() && self.np() > 0
        &&& self.echoes.ids@ =~= Seq::new(self.np(), |q: int| echo(self.id as int, q))
        &&& self.inbox.ids@  =~= Seq::new(self.np(), |r: int| echo(r, self.id as int))
        &&& self.echoes.iid() == self.log.iid()
        &&& self.inbox.iid()  == self.log.iid()
        &&& self.dec.iid()    == self.log.iid()
    }

    /// Commit to echoing `v`, then tell everyone. The log entry comes first and
    /// every echo points at it, which is what makes the commitment binding.
    pub fn echo_once(&mut self, v: u64)
        requires old(self).inv(), old(self).log.hist().len() == 0,
        ensures  final(self).inv(), final(self).np() == old(self).np(),
    {
        proof { lemma_shapes(self.id as int, 0); }
        let Tracked(w) = self.log.send(RMsg::LEcho(v));

        let mut i: usize = 0;
        while i < self.echoes.count()
            invariant
                0 <= i <= self.np(), self.inv(),
                w.instance_id() == self.log.iid(),
                w.element() == (elog(self.id as int), 0nat, RMsg::LEcho(v)),
            decreases self.np() - i,
        {
            proof { lemma_shapes(self.id as int, i as int); }
            self.echoes.send_caused(i, RMsg::Echo(v), Tracked(&w));
            i = i + 1;
        }
    }

    /// Wait for a quorum of echoes of `v`, then deliver.
    ///
    /// The one send in this protocol justified by a SET of causes: the whole
    /// quorum, whose size is not known when `Rbc` is written.
    pub fn gather_and_deliver(&mut self, v: u64)
        requires old(self).inv(),
        ensures  final(self).inv(), final(self).np() == old(self).np(),
    {
        let ghost me = self.id as int;
        proof { lemma_procs(); }

        let need = self.inbox.count() / 2 + 1;
        assert(need + need > n_proc()) by { assert(self.np() / 2 + self.np() / 2 >= self.np() - 1); }

        let accept = |k: usize, m: &RMsg| -> (r: bool)
            ensures r == (*m is Echo && m->Echo_0 == v)
        {
            match m { RMsg::Echo(w) => *w == v, _ => false }
        };
        let ghost pspec = |k: int, m: RMsg| m is Echo && m->Echo_0 == v;
        let (srcs, msgs, Tracked(cs), Ghost(poss)) =
            self.inbox.collect(need, Ghost(pspec), accept);

        let ghost sseq = Seq::new(need as nat, |j: int| srcs@[j] as int);
        let ghost q = sseq.to_set();
        proof {
            sseq.to_set_ensures();
            assert(sseq.no_duplicates());
            sseq.unique_seq_to_set();

            // Every source really echoed `v` to this node.
            assert forall|j: int| 0 <= j < need as int implies
                #[trigger] echoed(cs.set(), srcs@[j] as int, me, v) by {
                assert(pspec(srcs@[j] as int, msgs@[j]));
                assert(self.inbox.id(srcs@[j] as int) == echo(srcs@[j] as int, me));
                assert(msgs@[j] == RMsg::Echo(v));
                assert(cs.set().contains((echo(srcs@[j] as int, me), poss[j], RMsg::Echo(v))));
            }
            assert forall|a: int| q.contains(a) implies echoed(cs.set(), a, me, v) by {
                let j = choose|j: int| 0 <= j < sseq.len() && sseq[j] == a;
            }
            assert(is_quorum(q)) by {
                assert forall|a: int| q.contains(a) implies procs().contains(a) by {
                    let j = choose|j: int| 0 <= j < sseq.len() && sseq[j] == a;
                    assert(srcs@[j] < self.np());
                }
            }
            assert(quorum_echoed(cs.set(), me, v));
            lemma_shapes(me, 0);
            assert(self.dec.id().ix[0] == me) by { assert(seq![me][0] == me); }
        }
        self.dec.send_general(RMsg::Deliver(v), Tracked(&cs));
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Safety
// ---------------------------------------------------------------------------

/// A PROCESS ECHOES AT MOST ONE VALUE.
///
/// The step the whole protocol turns on, and the one that is only sayable
/// because every echo carries provenance back to a log that takes one entry.
/// Note what it relates: two echoes by the same process to DIFFERENT
/// destinations, on two channels no gate sees together.
pub proof fn lemma_echo_unique(
    ws: Set<(ChanId, nat, RMsg)>, p: int, q1: int, q2: int, v1: u64, v2: u64,
)
    requires
        rec_echo_logged(ws), rec_elog_once(ws), rec_functional(ws),
        echoed(ws, p, q1, v1), echoed(ws, p, q2, v2),
    ensures
        v1 == v2,
{
    lemma_shapes(p, q1);
    lemma_shapes(p, q2);
    let i1 = choose|i: nat| ws.contains((echo(p, q1), i, RMsg::Echo(v1)));
    let i2 = choose|i: nat| ws.contains((echo(p, q2), i, RMsg::Echo(v2)));
    // Both echoes point at position zero of the same log, so they point at the
    // same entry, so they carry the same value.
    assert(ws.contains((elog(p), 0, RMsg::LEcho(v1))));
    assert(ws.contains((elog(p), 0, RMsg::LEcho(v2))));
    lemma_elog_functional(ws, p, v1, v2);
}

/// One position of one channel holds one message. This is `NetSM::agree` read
/// back through the record: the machine's own invariant, not a protocol fact.
pub proof fn lemma_elog_functional(
    ws: Set<(ChanId, nat, RMsg)>, p: int, v1: u64, v2: u64,
)
    requires
        ws.contains((elog(p), 0, RMsg::LEcho(v1))),
        ws.contains((elog(p), 0, RMsg::LEcho(v2))),
        rec_functional(ws),
    ensures v1 == v2,
{
}

/// `p` delivered `v`.
pub open spec fn delivered(ws: Set<(ChanId, nat, RMsg)>, p: int, v: u64) -> bool {
    exists|i: nat| ws.contains((dlog(p), i, RMsg::Deliver(v)))
}

/// AGREEMENT.
///
/// No two processes ever deliver different values. Two quorums intersect, and
/// the process in both echoed once.
pub proof fn lemma_agreement(
    ws: Set<(ChanId, nat, RMsg)>, p1: int, v1: u64, p2: int, v2: u64,
)
    requires
        Rbc::record_inv(ws),
        delivered(ws, p1, v1), delivered(ws, p2, v2),
    ensures
        v1 == v2,
{
    lemma_shapes(p1, 0);
    lemma_shapes(p2, 0);
    let i1 = choose|i: nat| ws.contains((dlog(p1), i, RMsg::Deliver(v1)));
    let i2 = choose|i: nat| ws.contains((dlog(p2), i, RMsg::Deliver(v2)));
    assert(quorum_echoed(ws, p1, v1));
    assert(quorum_echoed(ws, p2, v2));

    let s1 = choose|s: Set<int>| is_quorum(s) && forall|p: int| s.contains(p) ==> echoed(ws, p, p1, v1);
    let s2 = choose|s: Set<int>| is_quorum(s) && forall|p: int| s.contains(p) ==> echoed(ws, p, p2, v2);
    lemma_quorum_intersect(s1, s2);
    let r = choose|r: int| s1.contains(r) && s2.contains(r);

    lemma_echo_unique(ws, r, p1, p2, v1, v2);
}

} // verus!
