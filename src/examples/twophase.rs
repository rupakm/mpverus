// PROOF-LEVEL, and structurally so.
//
// This is the two-phase commit that demonstrates the synchronised asynchronous
// call: the coordinator mints a private reply channel per call, and the
// handler's reply is absorbed at the call site, so the whole exchange is one
// atomic action with no interference point.
//
// It cannot be run, and adding a participant service would not help. The reply
// channel is `dyn_chan(1, j, k)`, created by the COORDINATOR at call time, so a
// participant would need the send endpoint of a channel somebody else made --
// and an endpoint cannot travel over a channel. The same missing capability
// blocks writers that arrive at run time and any accept-a-connection pattern.
//
// `twophase_fanout.rs` is the runnable two-phase commit: static per-participant
// channels, a real `Participant` service, and no atomicity claim.

use vstd::prelude::*;
use vstd::tokens::{InstanceId, MapToken, KeyValueToken, ElementToken, ValueToken};
use crate::tok::*;
use crate::proc::*;

verus! {

pub uninterp spec fn n_parts() -> int;
/// Participant j's vote. Fixed, and unknown to the coordinator's CODE -- it is
/// a ghost constant the proof may mention but the program cannot read.
pub uninterp spec fn vote(j: int) -> bool;
/// Coordinator -> participant j.
pub open spec fn req_chan(j: int) -> ChanId { chan(0, seq![j]) }
/// Participant j's k-th REPLY channel. Encoding the owner in the channel id is
/// what lets the send gate be a function of the channel alone, with no history_inv
/// state to track who a dynamically minted channel belongs to.
pub open spec fn rsp_chan(j: int, k: nat) -> ChanId { dyn_chan(1, j, k) }

/// The only assumption: how many participants there are.
#[verifier::external_body]
pub proof fn n_parts_nonneg()
    ensures
        n_parts() >= 0,
{
}

/// The facts call sites need. Everything except the participant count is
/// proved rather than assumed.
/// Note in particular that `rsp_chan` being injective in BOTH the owner and the
/// call counter -- which is what lets a dynamically minted channel be gated by
/// its owner, and what makes allocation fresh -- is now a theorem.
pub proof fn config()
    ensures
        n_parts() >= 0,
        forall|j: int, k: nat, j2: int, k2: nat|
            #[trigger] rsp_chan(j, k) == #[trigger] rsp_chan(j2, k2) ==> j == j2 && k == k2,
        forall|j: int, j2: int, k: nat|
            #[trigger] req_chan(j) != #[trigger] rsp_chan(j2, k),
        forall|j: int, j2: int| j != j2
            ==> #[trigger] req_chan(j) != #[trigger] req_chan(j2),
{
    n_parts_nonneg();
    assert forall|j: int, k: nat, j2: int, k2: nat|
        #[trigger] rsp_chan(j, k) == #[trigger] rsp_chan(j2, k2) implies j == j2 && k == k2 by {
        lemma_chan_inj2(1, j, k as int, j2, k2 as int);
    }
    assert forall|j: int, j2: int| j != j2
        implies #[trigger] req_chan(j) != #[trigger] req_chan(j2) by {
        if req_chan(j) == req_chan(j2) { lemma_chan_inj1(0, j, j2); }
    }
}

/// Only the prepare phase is modelled here: the participant's reply is
/// absorbed at the call site by `rpc`, so there is no participant function and
/// no decide broadcast.
pub enum Msg { Prepare(Ghost<ChanId>), Vote(bool) }

/// The gate, as a pure function of the channel: only participant j's own vote
/// may appear on a channel belonging to participant j.
pub open spec fn reply_ok(c: ChanId, m: Msg) -> bool {
    forall|j: int, k: nat| c == #[trigger] rsp_chan(j, k) ==> m == Msg::Vote(vote(j))
}

} // verus!

verus!{
/// The protocol. Its allocator, freshness invariant and channel naming are all
/// provided by `NetSM`; what remains is the message guarantee.
pub struct Tpc;

impl NetInv<Msg> for Tpc {
    /// Only participant j's own vote may appear on a channel belonging to j.
    open spec fn gate(c: ChanId, s: Seq<Msg>, m: Msg) -> bool { reply_ok(c, m) }

    open spec fn wit_inv(c: ChanId, m: Msg) -> bool { reply_ok(c, m) }

    open spec fn deliverable_at(v: Seq<Msg>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn history_inv(sent: Map<ChanId, Seq<Msg>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn pair_gives(c: ChanId, m1: Msg, m2: Msg) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<Msg>>, c: ChanId,
                                i: nat, j: nat, m1: Msg, m2: Msg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Msg>, m: Msg) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Msg) -> bool { false }
    open spec fn caused_by(c: ChanId, m: Msg, causes: Set<(ChanId, nat, Msg)>) -> bool { false }
    open spec fn caused_by1(c: ChanId, m: Msg, d: ChanId, j: nat, m2: Msg) -> bool { false }
    proof fn lemma_caused_by1(c: ChanId, m: Msg, d: ChanId, j: nat, m2: Msg) { }

    open spec fn cause_gives(c: ChanId, m: Msg) -> bool { true }
    proof fn lemma_cause_gives(c: ChanId, m: Msg, causes: Set<(ChanId, nat, Msg)>) { }
    // No cross-channel property to state over the record.
    open spec fn record_inv(was_sent: Set<(ChanId, nat, Msg)>) -> bool { true }
    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, Msg)>,
                                     sent: Map<ChanId, Seq<Msg>>,
                                     c: ChanId, s: Seq<Msg>, m: Msg,
                                     causes: Set<(ChanId, nat, Msg)>) { }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<Msg>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<Msg>>,
                                   was_sent: Set<(ChanId, nat, Msg)>,
                                   c: ChanId, s: Seq<Msg>, m: Msg,
                                   causes: Set<(ChanId, nat, Msg)>) { }
}

/// Per-link FIFO delivery is deterministic, so this protocol may use `rpc`.
impl DetDelivery<Msg> for Tpc {
    proof fn lemma_delivery_determined(v: Seq<Msg>, i: nat, j: nat) {
        lemma_fifo_determined(v, i, j);
    }
}

/// The coordinator. Each round mints its own reply channel per participant and
/// makes ONE remote call, which -- being `L . L` -- contains no interference
/// point at all, so the loop is a plain sequential loop.
pub struct TpcCoordinator {
    pub reqs: FanOut<Msg, Tpc>,
    /// The channel allocator. Reply channels are created while the program
    /// runs, one per call, and freshness is the machine's business.
    pub alloc: Tracked<NetSM::next<Msg, Tpc>>,
    /// A handle to the machine, so opening a reply channel needs no endpoint.
    pub inst: Tracked<NetSM::Instance<Msg, Tpc>>,
    pub committed: bool,
}

impl TpcCoordinator {
    pub open spec fn inv(&self) -> bool {
        &&& self.reqs.wf()
        &&& self.reqs.len() as int == n_parts()
        &&& self.alloc@.instance_id() == self.inst@.id()
        &&& self.reqs.iid() == self.inst@.id()
        &&& self.reqs.ids@ =~= Seq::new(n_parts() as nat, |j: int| req_chan(j))
    }

    pub fn run_round(&mut self) -> (committed: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            // SAFETY: commit only if every participant voted yes.
            committed ==> forall|j: int| 0 <= j < n_parts() ==> vote(j),
    {
        let mut i: usize = 0;
        let mut all_yes: bool = true;

        while i < self.reqs.count() && all_yes
            invariant
                0 <= i <= n_parts(),
                self.inv(),
                all_yes ==> forall|j: int| 0 <= j < i ==> vote(j),
            decreases n_parts() - i,
        {
            proof { config(); }
            let ghost iid = self.inst@.id();

            // Open this call's private reply channel.
            let (reply_out, mut reply_in) = open_new_channel::<Msg, Tpc>(
                Ghost(1), i, Tracked(self.inst.borrow()),
                Tracked(self.alloc.borrow_mut()));

            let ghost expected = Msg::Vote(vote(i as int));
            proof {
                // Gate for the request send: a request channel is nobody's
                // reply channel.
                assert forall|j2: int, k2: nat|
                    self.reqs.id(i as int) == #[trigger] rsp_chan(j2, k2)
                    implies Msg::Prepare(Ghost(reply_in.id())) == Msg::Vote(vote(j2)) by {
                    assert(req_chan(i as int) != rsp_chan(j2, k2));
                }
                // Gate for the absorbed reply: the channel belongs to
                // participant i, so only participant i's vote may go on it --
                // and that is what we are about to put there.
                assert forall|j2: int, k2: nat| reply_in.id() == #[trigger] rsp_chan(j2, k2)
                    implies expected == Msg::Vote(vote(j2)) by {
                    assert(j2 == i as int);
                }
            }

            // One atomic action: send, absorb the handler, take the reply.
            let m = self.reqs.call(
                i, Msg::Prepare(Ghost(reply_in.id())), &mut reply_in,
                Tracked(reply_out.tok.get()), Ghost(expected));

            match m {
                Msg::Vote(b) => { if !b { all_yes = false; } }
                _ => { all_yes = false; }
            }
            i = i + 1;
        }

        all_yes
    }
}

impl Process for TpcCoordinator {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { self.committed = self.run_round(); }
}
}
