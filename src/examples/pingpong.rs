// Ping-pong: the smallest protocol that exercises every part of the method.
//
// Two parties and two channels. A sends `Ping` to B; B answers with `Pong(v)`
// for some well-formed payload `v`; A receives it and knows the payload is well
// formed, without having reasoned about B's code.
//
// This is the example the write-up walks through. Read it alongside `NetSM` in
// `src/tok.rs`: the machine there is what gives these definitions their
// meaning, and the whole of a protocol is the implementation below.

use vstd::prelude::*;
use vstd::tokens::KeyValueToken;
use crate::tok::*;
use crate::proc::*;

verus! {

/// What a well-formed payload is. Left abstract: the protocol does not care.
pub uninterp spec fn ok(v: u64) -> bool;

/// The two channels. Built with `chan`, so their distinctness follows from how
/// they are named rather than being assumed.
pub open spec fn ping_chan() -> ChanId { chan(0, seq![]) }
pub open spec fn pong_chan() -> ChanId { chan(1, seq![]) }

pub proof fn lemma_chans_differ()
    ensures ping_chan() != pong_chan(),
{
    lemma_chan_distinct(0, seq![], 1, seq![]);
}

#[derive(Structural, PartialEq, Eq)]
pub enum Msg { Ping, Pong(u64) }

/// The one predicate the protocol is about: an answer is a well-formed `Pong`.
/// Nothing is claimed about the request channel.
///
/// It is used twice below, as the gate on sending and as the guarantee about
/// what was sent. Those two roles being the same predicate is the usual case,
/// and is why `lemma_gate_gives_inv` is empty.
pub open spec fn pong_ok(c: ChanId, m: Msg) -> bool {
    c == pong_chan() ==> (m is Pong && ok(m->Pong_0))
}

/// The protocol.
pub struct PingPong;

impl NetInv<Msg> for PingPong {
    /// Placing a malformed answer on the answer channel is a failure of the
    /// program, not something to wait for.
    open spec fn gate(c: ChanId, s: Seq<Msg>, m: Msg) -> bool { pong_ok(c, m) }

    /// What may be concluded about a message that was sent.
    open spec fn wit_inv(c: ChanId, m: Msg) -> bool { pong_ok(c, m) }

    /// Per-link FIFO: the next message is the one at the current length.
    open spec fn deliverable_at(v: Seq<Msg>, i: nat) -> bool { fifo_deliverable(v, i) }

    /// No guarantee that a single message cannot express.
    open spec fn extra(sent: Map<ChanId, Seq<Msg>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn extra_gives2(c: ChanId, m1: Msg, m2: Msg) -> bool { true }
    proof fn lemma_extra_gives2(sent: Map<ChanId, Seq<Msg>>, c: ChanId,
                                i: nat, j: nat, m1: Msg, m2: Msg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Msg>, m: Msg) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Msg) -> bool { false }
    proof fn lemma_cause_gives(c: ChanId, m: Msg, causes: Set<(ChanId, nat, Msg)>) { }
    // No cross-channel property to state over the record.
    open spec fn extra_w(was_sent: Set<(ChanId, nat, Msg)>) -> bool { true }
    proof fn lemma_extra_w_init() { }

    proof fn lemma_extra_w_preserved(was_sent: Set<(ChanId, nat, Msg)>,
                                     c: ChanId, i: nat, m: Msg,
                                     causes: Set<(ChanId, nat, Msg)>) { }

    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_alloc(sent: Map<ChanId, Seq<Msg>>, c: ChanId) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<Msg>>,
                                   was_sent: Set<(ChanId, nat, Msg)>,
                                   c: ChanId, s: Seq<Msg>, m: Msg,
                                   causes: Set<(ChanId, nat, Msg)>) { }
}

/// Delivery here is deterministic, so this protocol could use a remote call.
impl DetDelivery<Msg> for PingPong {
    proof fn lemma_delivery_determined(v: Seq<Msg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}

// ---------------------------------------------------------------------------
// The two services, as HANDLERS.
//
// Neither ever blocks. The driver owns the mailbox and does the one blocking
// receive, so each turn is `R . N . L*` -- one atomic block -- and `wf` is
// required across the only point where another thread can interleave.
//
// Wrapping either in `Driven` gives a `Process`, so `run` drives it unchanged.
// ---------------------------------------------------------------------------

/// Answers requests. Purely reactive, so `tick` does nothing.
pub struct Responder {
    pub rsp: Out<Msg, PingPong>,
    /// The value this service serves. Well formed, which is what the gate on
    /// the answer channel demands.
    pub val: u64,
    /// Its mailbox is the request channel.
    pub inbox_chans: Ghost<Seq<ChanId>>,
}

impl NetHandler<Msg, PingPong> for Responder {
    open spec fn wf(&self) -> bool {
        &&& self.rsp.wf() && self.rsp.id() == pong_chan()
        &&& ok(self.val)
        &&& self.inbox_chans@ =~= seq![ping_chan()]
    }
    open spec fn iid(&self) -> InstanceId { self.rsp.iid() }
    open spec fn chans(&self) -> Seq<ChanId> { self.inbox_chans@ }

    fn tick(&mut self) { }

    fn handle(&mut self, from: usize, m: Msg, Tracked(w): Tracked<NetSM::was_sent<Msg, PingPong>>) {
        self.rsp.send(Msg::Pong(self.val));
    }
}

/// Asks, and knows the answer is well formed.
///
/// This service INITIATES, which is what `tick` is for. The state that used to
/// live between the send and the receive inside one activity is now a field:
/// that is what "a client is a state machine" means concretely.
///
/// Note this is also the RPC pattern. A request-response exchange is `tick`
/// sending and `handle` receiving, with the driver's blocking receive -- and
/// the `wf` check around it -- exactly in the middle. Two atomic blocks with a
/// checked invariant between them, not one atomic block; see `docs/plan.md` on
/// why a blocking call cannot honestly claim to be atomic.
pub struct Initiator {
    pub req:  Out<Msg, PingPong>,
    pub seen: u64,
    /// Whether an answer has been received, and so whether `seen` means
    /// anything.
    pub got:  bool,
    pub waiting: bool,
    pub inbox_chans: Ghost<Seq<ChanId>>,
}

impl NetHandler<Msg, PingPong> for Initiator {
    open spec fn wf(&self) -> bool {
        &&& self.req.wf() && self.req.id() == ping_chan()
        &&& self.inbox_chans@ =~= seq![pong_chan()]
        // The protocol's guarantee, carried in this service's own invariant.
        &&& self.got ==> ok(self.seen)
        // A fact established BEFORE the request and used AFTER the reply, i.e.
        // one that must survive the interference point in between. It does,
        // and not because anything was proved about other threads: this is a
        // fact about a send history THIS service owns, and nobody else can
        // append to it. That is the whole reason a blocking exchange needs no
        // atomicity argument here.
        &&& self.waiting ==> self.req.hist().len() > 0
    }
    open spec fn iid(&self) -> InstanceId { self.req.iid() }
    open spec fn chans(&self) -> Seq<ChanId> { self.inbox_chans@ }

    fn tick(&mut self) {
        if !self.waiting {
            proof { lemma_chans_differ(); }
            self.req.send(Msg::Ping);
            self.waiting = true;
        }
    }

    fn handle(&mut self, from: usize, m: Msg, Tracked(w): Tracked<NetSM::was_sent<Msg, PingPong>>) {
        // Still true, across the yield.
        assert(self.waiting ==> self.req.hist().len() > 0);
        match m {
            Msg::Pong(v) => { self.seen = v; self.got = true; self.waiting = false; }
            // The guarantee rules this out: the answer channel carries only Pongs.
            Msg::Ping    => { proof { assert(false); } }
        }
    }
}

/// `(R . N . L*)*` -- repeated rounds.
///
/// Each turn is one atomic block; between turns the invariant holds and other
/// threads run. That is a SEQUENCE of atomic blocks, not one big one, which is
/// the correct reading: `R . N . L*` reduces, `(R . N . L*)*` does not, and
/// nothing here claims it does.
pub fn run_rounds(d: &mut Driven<Msg, PingPong, Initiator>, rounds: usize)
    requires old(d).wf(),
    ensures
        final(d).wf(),
        // Whatever happened across the rounds, anything received was an answer
        // the protocol vouches for.
        final(d).h.got ==> ok(final(d).h.seen),
{
    run(d, rounds);
    assert(d.h.wf());
}

} // verus!
