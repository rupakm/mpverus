// An unreliable link: messages may be lost or duplicated.
//
// Two things are independent here, and it is easy to conflate them:
//
//   * who may send decides whether a send history can be exclusively owned,
//     and therefore whether `send` is a left mover. Several senders require a
//     family of channels; see `collector.rs`.
//   * the delivery discipline decides what a receiver may be handed. It is a
//     property of the receive side alone.
//
// Unreliability is of the second kind. A lossy link has one sender and one
// receiver, being a datagram link rather than a shared mailbox, so ownership is
// unaffected and the entire difference from per-link FIFO is one line:
//
//     deliverable_at(v, i) == true      // any index, any number of times
//
// Loss requires no modelling: nothing here forces a delivery, so a message that
// never arrives leaves its receiver blocked. Duplication is the absence of the
// index constraint, and it is expressible because witnesses are persistent: a
// witness is duplicable and is never retracted, so returning the same one twice
// is what a duplicating network does.
//
// What survives unchanged is any invariant of the form "everything ever sent
// satisfies P", since that is a statement about the send history. What does not
// survive is counting; `counterexamples/lossy_counting.rs` records the
// difference.

use vstd::prelude::*;
use vstd::tokens::KeyValueToken;
use crate::tok::*;
use crate::proc::*;

verus! {

/// What a well-formed payload looks like. Left abstract.
pub uninterp spec fn ok(v: u64) -> bool;

/// The link this protocol is about.
pub uninterp spec fn link() -> ChanId;

#[derive(Structural, PartialEq, Eq)]
pub struct Pkt { pub v: u64 }

/// The protocol. Everything it says about its messages is these four
/// definitions and three proofs; there is no state machine to write.
pub struct Lossy;

impl NetInv<Pkt> for Lossy {
    /// Putting a malformed payload on the link is a failure of the program,
    /// not something to wait for.
    open spec fn gate(c: ChanId, s: Seq<Pkt>, m: Pkt) -> bool {
        c == link() ==> ok(m.v)
    }

    /// The guarantee about anything already sent. The gate again: what may be
    /// placed on the link is what everything on the link satisfies.
    open spec fn wit_inv(c: ChanId, m: Pkt) -> bool {
        c == link() ==> ok(m.v)
    }

    /// The entire difference from a reliable link.
    open spec fn deliverable_at(v: Seq<Pkt>, i: nat) -> bool { true }

    /// No guarantee that a single message cannot express.
    open spec fn extra(sent: Map<ChanId, Seq<Pkt>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn extra_gives2(c: ChanId, m1: Pkt, m2: Pkt) -> bool { true }
    proof fn lemma_extra_gives2(sent: Map<ChanId, Seq<Pkt>>, c: ChanId,
                                i: nat, j: nat, m1: Pkt, m2: Pkt) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Pkt>, m: Pkt) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Pkt) -> bool { false }
    proof fn lemma_cause_gives(c: ChanId, m: Pkt, causes: Set<(ChanId, nat, Pkt)>) { }
    // No cross-channel property to state over the record.
    open spec fn extra_w(was_sent: Set<(ChanId, nat, Pkt)>) -> bool { true }
    proof fn lemma_extra_w_init() { }

    proof fn lemma_extra_w_preserved(was_sent: Set<(ChanId, nat, Pkt)>,
                                     c: ChanId, i: nat, m: Pkt,
                                     causes: Set<(ChanId, nat, Pkt)>) { }

    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_alloc(sent: Map<ChanId, Seq<Pkt>>, c: ChanId) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<Pkt>>,
                                   was_sent: Set<(ChanId, nat, Pkt)>,
                                   c: ChanId, s: Seq<Pkt>, m: Pkt,
                                   causes: Set<(ChanId, nat, Pkt)>) { }
}

// ---------------------------------------------------------------------------
// The two services.
// ---------------------------------------------------------------------------

/// The sender. Its shape is the same as on a reliable link: `send` remains a
/// left mover, because `deliverable_at` is still monotone in the send history.
pub struct Transmitter {
    pub link: Out<Pkt, Lossy>,
    /// The value this service sends. Well formed, which the gate demands.
    pub v: u64,
}

impl Process for Transmitter {
    open spec fn wf(&self) -> bool {
        self.link.wf() && self.link.id() == link() && ok(self.v)
    }

    fn step(&mut self) {
        self.link.send(Pkt { v: self.v });
    }
}

/// The receiver. Every packet handed to it was in fact sent, and therefore
/// satisfies the protocol's guarantee. Duplication does not weaken this,
/// because the guarantee is a statement about the send history.
pub struct Sink {
    pub link: In<Pkt, Lossy>,
    pub last: u64,
}

impl Sink {
    pub open spec fn inv(&self) -> bool {
        self.link.wf() && self.link.id() == link()
    }

    pub fn receive_one(&mut self) -> (p: Pkt)
        requires old(self).inv(),
        ensures  final(self).inv(), ok(p.v),
    {
        self.link.recv()
    }

    /// Two receives still yield two well-formed packets. What they do not
    /// establish is that the two came from distinct sends; see
    /// `counterexamples/lossy_counting.rs`.
    pub fn receive_two(&mut self) -> (r: (Pkt, Pkt))
        requires old(self).inv(),
        ensures  final(self).inv(), ok(r.0.v), ok(r.1.v),
    {
        let a = self.receive_one();
        let b = self.receive_one();
        (a, b)
    }
}

impl Process for Sink {
    open spec fn wf(&self) -> bool { self.inv() }

    fn step(&mut self) {
        let p = self.receive_one();
        self.last = p.v;
    }
}

} // verus!
