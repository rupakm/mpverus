// A heartbeat on a link with a single sender.
//
// This example turns on ownership. A thread that is the only sender on a link
// still knows, after an interference point, exactly what it last wrote there.
// It knows this because it holds the link's send token: no other thread can
// hold that token, so no other thread can append, and the fact does not have to
// be re-established. The proof following the interference point is empty.
use vstd::prelude::*;
use vstd::tokens::InstanceId;
use crate::tok::*;
use crate::proc::*;
use crate::layer::Layered;

verus!{
#[derive(Structural, PartialEq, Eq)]
pub struct Beat { pub seq: u64 }


}

verus!{
/// The protocol. Its guarantee is about PAIRS of messages -- each beat's
/// sequence number exceeds every earlier one -- which no statement about a
/// single message can express. So `wit_inv` is trivial and the guarantee is
/// carried by `history_inv`, the invariant over the send histories.
pub struct HbTok;

/// The link this node beats on.
pub uninterp spec fn link() -> ChanId;

impl NetInv<Beat> for HbTok {
    /// A tick may only extend the sequence; regressing is a failure, not a
    /// wait. Stated for every channel, which is stronger than needed and costs
    /// nothing here.
    open spec fn gate(c: ChanId, s: Seq<Beat>, m: Beat) -> bool {
        forall|x: int| 0 <= x < s.len() ==> (#[trigger] s[x]).seq < m.seq
    }

    /// Nothing a single witness can say.
    open spec fn wit_inv(c: ChanId, m: Beat) -> bool { true }

    open spec fn deliverable_at(v: Seq<Beat>, i: nat) -> bool { fifo_deliverable(v, i) }

    /// The guarantee: beats on the link are numbered increasingly.
    open spec fn history_inv(sent: Map<ChanId, Seq<Beat>>) -> bool {
        sent.dom().contains(link()) ==>
            forall|x: int, y: int| 0 <= x < y < sent[link()].len()
                ==> (#[trigger] sent[link()][x]).seq < (#[trigger] sent[link()][y]).seq
    }

    /// THE PAIRWISE GUARANTEE, in the form a reader can use. `wit_inv` is
    /// `true` here because a witness names one message and this is about two;
    /// `history_inv` states it over the histories, and this is how it comes back out
    /// to someone who does not own the link.
    open spec fn pair_gives(c: ChanId, m1: Beat, m2: Beat) -> bool {
        c == link() ==> m1.seq < m2.seq
    }

    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<Beat>>, c: ChanId,
                                i: nat, j: nat, m1: Beat, m2: Beat) {
        if c == link() {
            assert(sent[link()][i as int].seq < sent[link()][j as int].seq);
        }
    }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Beat>, m: Beat) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Beat) -> bool { false }
    open spec fn caused_by(c: ChanId, m: Beat, causes: Set<(ChanId, nat, Beat)>) -> bool { false }
    open spec fn cause_gives(c: ChanId, m: Beat) -> bool { true }
    proof fn lemma_cause_gives(c: ChanId, m: Beat, causes: Set<(ChanId, nat, Beat)>) { }

    // No cross-channel property to state over the record.
    open spec fn record_inv(was_sent: Set<(ChanId, nat, Beat)>) -> bool { true }
    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, Beat)>,
                                     sent: Map<ChanId, Seq<Beat>>,
                                     c: ChanId, s: Seq<Beat>, m: Beat,
                                     causes: Set<(ChanId, nat, Beat)>) { }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) {
        let s0 = Map::new(chans, |c: ChanId| Seq::<Beat>::empty());
        if s0.dom().contains(link()) { assert(s0[link()].len() == 0); }
    }

    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<Beat>>, c: ChanId) {
        let post = sent.insert(c, Seq::<Beat>::empty());
        if post.dom().contains(link()) {
            assert forall|x: int, y: int| 0 <= x < y < post[link()].len()
                implies (#[trigger] post[link()][x]).seq < (#[trigger] post[link()][y]).seq by {
                if c == link() { assert(post[link()].len() == 0); }
            }
        }
    }

    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<Beat>>,
                                   was_sent: Set<(ChanId, nat, Beat)>,
                                   c: ChanId, s: Seq<Beat>, m: Beat,
                                   causes: Set<(ChanId, nat, Beat)>) {
        let post = sent.insert(c, s.push(m));
        if post.dom().contains(link()) {
            // The link's history is untouched unless this send was on it, so
            // the quadratic ordering goal runs only in that branch.
            assert forall|x: int, y: int| 0 <= x < y < post[link()].len()
                implies (#[trigger] post[link()][x]).seq < (#[trigger] post[link()][y]).seq by {
                if c == link() { assert(post[link()] == s.push(m)); }
            }
        }
    }
}
}

// ---------------------------------------------------------------------------
// WHAT THE PROTOCOL SUPPLIES TO THE GENERIC LIBRARY. Mechanical: six one-line
// readers, the gate, and two delegations to the generated exchanges. Nothing here is
// ---------------------------------------------------------------------------
verus!{
/// The monitor: emits beats with strictly increasing sequence numbers, which
/// is the protocol's gate.
pub struct Monitor {
    pub link: Out<Beat, HbTok>,
    pub seq:  u64,
}

impl Monitor {
    pub open spec fn inv(&self) -> bool {
        &&& self.link.wf() && self.link.id() == link()
        // Everything already sent is below the next number to use.
        &&& forall|x: int| 0 <= x < self.link.hist().len()
                ==> (#[trigger] self.link.hist()[x]).seq < self.seq
    }

    /// Send a beat, then explicitly yield, and observe that the beat is still
    /// the last thing on the link. The conclusion holds only because this
    /// service owns the send side, and the proof after the yield is empty.
    pub fn beat_and_wait(&mut self)
        requires old(self).inv(), old(self).seq < u64::MAX,
        ensures
            final(self).inv(),
            final(self).link.hist().len() > 0,
            final(self).link.hist().last() == (Beat { seq: old(self).seq }),
    {
        let s = self.seq;
        let ghost h0 = self.link.hist();
        self.link.send(Beat { seq: s });
        self.seq = s + 1;
        assert forall|x: int| 0 <= x < self.link.hist().len()
            implies (#[trigger] self.link.hist()[x]).seq < self.seq by {
            if x < h0.len() { assert(self.link.hist()[x] == h0[x]); }
        }

        interference_point();

        // Nothing to prove here. Nobody else could have appended.
    }
}

impl Process for Monitor {
    open spec fn wf(&self) -> bool { self.inv() }
    /// Sequence numbers are finite. A monitor that has exhausted them stops
    /// beating rather than repeating one, which the gate would reject anyway.
    fn step(&mut self) {
        if self.seq < u64::MAX { self.beat_and_wait(); }
    }
}

/// The watcher.
pub struct Watcher {
    pub link: In<Beat, HbTok>,
    pub last: u64,
}

impl Watcher {
    pub open spec fn inv(&self) -> bool {
        self.link.wf() && self.link.id() == link()
    }

    /// THE CONTRAST WITH AN UNRELIABLE LINK. On per-link FIFO, two receives
    /// really do come from two distinct sends: `deliverable_at` pins the index
    /// to the current length, so consuming advances it. The identical claim on
    /// a lossy link is `counterexamples/lossy_counting.rs`, and it must fail.
    pub fn two_are_distinct(&mut self) -> (r: (Beat, Beat, Ghost<nat>, Ghost<nat>))
        requires old(self).inv(),
        ensures  final(self).inv(), r.2@ != r.3@,
    {
        let (a, Tracked(wa)) = self.link.recv_wit();
        let (b, Tracked(wb)) = self.link.recv_wit();
        (a, b, Ghost(wa.element().1), Ghost(wb.element().1))
    }

    /// THE PAYOFF. The watcher owns no send history and cannot read the link,
    /// yet it concludes that the two beats it was handed increase.
    ///
    /// Before `learn_pair` existed this was not statable: `history_inv` was proved
    /// and there was no way to get at it from code.
    pub fn two_increase(&mut self) -> (r: (Beat, Beat))
        requires old(self).inv(),
        ensures  final(self).inv(), r.0.seq < r.1.seq,
    {
        let ghost h0 = self.link.rhist();
        let (a, Tracked(wa)) = self.link.recv_wit();
        let (b, Tracked(wb)) = self.link.recv_wit();
        proof {
            // FIFO pins each index to the length at the time of the receive, so
            // the second is strictly after the first.
            assert(wa.element().1 == h0.len());
            assert(wb.element().1 == h0.push(a).len());
            self.link.inst.borrow().learn_pair(
                link(), wa.element().1, wb.element().1, a, b, &wa, &wb);
        }
        (a, b)
    }
}

impl Process for Watcher {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { let b = self.link.recv(); self.last = b.seq; }
}
}

verus!{
/// Heartbeat as the bottom of a refinement stack. Every clause names something
/// the machine already generated, so there is no second definition to drift.
impl Layered<Beat> for HbTok {
    type St = NetSM::State<Beat, HbTok>;

    open spec fn st_inv(s: NetSM::State<Beat, HbTok>) -> bool { s.invariant() }

    /// The state-level form of the gate. This one is given the state, so
    /// unlike `NetInv::gate` it can name the link, and it says only
    /// what the layer above needs: the machine's own precondition is stronger,
    /// which is what `lemma_send_gate_st` checks.
    open spec fn st_send_gate(s: NetSM::State<Beat, HbTok>, c: ChanId, m: Beat) -> bool {
        (c == link() && s.sent.dom().contains(c)) ==>
            forall|x: int| 0 <= x < s.sent[c].len()
                ==> (#[trigger] s.sent[c][x]).seq < m.seq
    }

    open spec fn st_send(s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>, c: ChanId,
                         q: Seq<Beat>, m: Beat) -> bool {
        <NetSM::State<Beat, HbTok>>::do_send(s0, s1, c, q, m, Set::empty())
    }

    open spec fn st_recv(s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>, c: ChanId,
                         q: Seq<Beat>, m: Beat) -> bool {
        exists|i: nat| <NetSM::State<Beat, HbTok>>::do_recv(s0, s1, c, q, i, m)
    }

    proof fn lemma_send_gate_st(s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>, c: ChanId,
                                q: Seq<Beat>, m: Beat) {
        // The machine's `require` is a conjunct of its own transition relation,
        // and `q` is `s0`'s history for `c`, so the gate falls straight out.
    }
}
}
