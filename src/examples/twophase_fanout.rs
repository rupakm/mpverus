// Two-phase commit, fan-out form, on tokens.
//
// The coordinator broadcasts Prepare to everyone WITHOUT waiting, then collects
// responses in a loop, breaking out at the first No. There is no RPC here, so
// nothing hides the interference: every collect is an interference point, and
// other participants reply while the coordinator is blocked.
//
// That makes the YIELD INVARIANT do the work. In the RPC version the caller
// learns what the server computed by absorbing the handler's action; here it
// learns it from an invariant relating messages on a reply channel to the
// participant that owns it -- cashed in by `In::recv`, using the
// witness that `recv` hands back.

use vstd::prelude::*;
use vstd::tokens::{InstanceId, MapToken, KeyValueToken, ElementToken};
use crate::tok::*;
use crate::proc::*;

verus! {

// ---------------------------------------------------------------------------
// Configuration. Protocol parameters, not soundness assumptions.
// ---------------------------------------------------------------------------

pub uninterp spec fn n_parts() -> int;
/// Participant j's vote. Fixed but unknown to the coordinator.
pub uninterp spec fn vote(j: int) -> bool;
/// Coordinator -> participant j, and participant j -> coordinator.
/// Concrete channel names, so distinctness is structural rather than assumed:
/// different families cannot collide, and within a family the index decides.
pub open spec fn req_chan(j: int) -> ChanId { chan(0, seq![j]) }
pub open spec fn rsp_chan(j: int) -> ChanId { chan(1, seq![j]) }

/// The only assumption: how many participants there are.
#[verifier::external_body]
pub proof fn n_parts_nonneg()
    ensures
        n_parts() >= 0,
{
}

/// The facts call sites need. Everything except the participant count is
/// proved rather than assumed:
/// that participants have distinct channels, and that a request channel is
/// never a reply channel, follow from how the names are built.
pub proof fn config()
    ensures
        n_parts() >= 0,
        forall|j: int, k: int| j != k
            ==> #[trigger] req_chan(j) != #[trigger] req_chan(k),
        forall|j: int, k: int| j != k
            ==> #[trigger] rsp_chan(j) != #[trigger] rsp_chan(k),
        forall|j: int, k: int| #[trigger] req_chan(j) != #[trigger] rsp_chan(k),
{
    n_parts_nonneg();
    assert forall|j: int, k: int| j != k
        implies #[trigger] req_chan(j) != #[trigger] req_chan(k) by {
        if req_chan(j) == req_chan(k) { lemma_chan_inj1(0, j, k); }
    }
    assert forall|j: int, k: int| j != k
        implies #[trigger] rsp_chan(j) != #[trigger] rsp_chan(k) by {
        if rsp_chan(j) == rsp_chan(k) { lemma_chan_inj1(1, j, k); }
    }
}

#[derive(Structural, PartialEq, Eq)]
pub enum FMsg { Prepare, Vote(bool) }

/// Is `c` participant `j`'s reply channel?
pub open spec fn is_rsp(c: ChanId, j: int) -> bool {
    0 <= j < n_parts() && c == rsp_chan(j)
}

} // verus!

verus!{
/// The protocol. Everything it says about its messages is these four
/// definitions and four proofs; there is no state machine to write.
pub struct TpcfTok;

impl NetInv<FMsg> for TpcfTok {
    open spec fn gate(c: ChanId, s: Seq<FMsg>, m: FMsg) -> bool {
        forall|j: int| #[trigger] is_rsp(c, j) ==> m == FMsg::Vote(vote(j))
    }

    open spec fn wit_inv(c: ChanId, m: FMsg) -> bool {
        forall|j: int| #[trigger] is_rsp(c, j) ==> m == FMsg::Vote(vote(j))
    }

    open spec fn deliverable_at(v: Seq<FMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn extra(sent: Map<ChanId, Seq<FMsg>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn extra_gives2(c: ChanId, m1: FMsg, m2: FMsg) -> bool { true }
    proof fn lemma_extra_gives2(sent: Map<ChanId, Seq<FMsg>>, c: ChanId,
                                i: nat, j: nat, m1: FMsg, m2: FMsg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<FMsg>, m: FMsg) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: FMsg) -> bool { false }
    proof fn lemma_cause_gives(c: ChanId, m: FMsg, causes: Set<(ChanId, nat, FMsg)>) { }
    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_alloc(sent: Map<ChanId, Seq<FMsg>>, c: ChanId) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<FMsg>>, c: ChanId,
                                   s: Seq<FMsg>, m: FMsg) { }
}
}

// ---------------------------------------------------------------------------
// THE PROTOCOL. Ordinary sequential Rust on both sides.
// ---------------------------------------------------------------------------
verus!{
// ---------------------------------------------------------------------------
// The two kinds of service.
// ---------------------------------------------------------------------------

/// Participant j: block for the request, then answer with its own vote.
/// `R . L` -- one interference point, at the receive.
pub struct Participant {
    pub j:   usize,
    pub req: In<FMsg, TpcfTok>,
    pub rsp: Out<FMsg, TpcfTok>,
    pub my_vote: bool,
}

impl Process for Participant {
    open spec fn wf(&self) -> bool {
        &&& self.req.wf() && self.rsp.wf()
        &&& 0 <= self.j < n_parts()
        &&& self.my_vote == vote(self.j as int)
        &&& self.req.id() == req_chan(self.j as int)
        &&& self.rsp.id() == rsp_chan(self.j as int)
    }

    fn step(&mut self) {
        proof { config(); }
        // A right mover, and the only interference point in this block.
        let _m = self.req.recv();
        // A left mover. The gate restricts this: only participant j's own vote
        // may be placed on this channel.
        self.rsp.send(FMsg::Vote(self.my_vote));
    }
}

/// Participant `j`'s endpoints are the ones they should be. Stated over the
/// vectors, so that changing one of them leaves the rest alone.
pub open spec fn tpcf_pair_ok(
    reqs: Seq<Out<FMsg, TpcfTok>>, rsps: Seq<In<FMsg, TpcfTok>>, j: int,
) -> bool {
    &&& reqs[j].wf() && rsps[j].wf()
    &&& reqs[j].id() == req_chan(j)
    &&& rsps[j].id() == rsp_chan(j)
}

/// The coordinator. Broadcast without waiting, then gather with an early exit.
pub struct Coordinator {
    pub reqs: Vec<Out<FMsg, TpcfTok>>,
    pub rsps: Vec<In<FMsg, TpcfTok>>,
    pub committed: bool,
}

impl Coordinator {
    pub open spec fn inv(&self) -> bool {
        &&& self.reqs.len() as int == n_parts()
        &&& self.rsps.len() as int == n_parts()
        &&& forall|j: int| 0 <= j < n_parts()
                ==> #[trigger] tpcf_pair_ok(self.reqs@, self.rsps@, j)
    }

    /// One round of the protocol.
    pub fn run_round(&mut self) -> (committed: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            // Commit only if every participant voted yes.
            committed ==> forall|j: int| 0 <= j < n_parts() ==> vote(j),
    {
        proof { config(); }

        // ---- phase 1: broadcast, no waiting ----
        // Every send is a left mover, so the whole loop is one atomic block.
        let mut i: usize = 0;
        while i < self.reqs.len()
            invariant
                0 <= i <= n_parts(),
                self.inv(),
            decreases n_parts() - i,
        {
            let ghost r0 = self.reqs@;
            assert(tpcf_pair_ok(self.reqs@, self.rsps@, i as int));
            self.reqs[i].send(FMsg::Prepare);
            assert forall|j: int| 0 <= j < n_parts()
                implies #[trigger] tpcf_pair_ok(self.reqs@, self.rsps@, j) by {
                assert(tpcf_pair_ok(r0, self.rsps@, j));
                if j != i as int { assert(self.reqs@[j] == r0[j]); }
            }
            i = i + 1;
        }

        // ---- phase 2: collect, stopping at the first No ----
        let mut k: usize = 0;
        let mut all_yes: bool = true;

        while k < self.rsps.len() && all_yes
            invariant
                0 <= k <= n_parts(),
                self.inv(),
                all_yes ==> forall|j: int| 0 <= j < k ==> vote(j),
            decreases n_parts() - k,
        {
            let ghost s0 = self.rsps@;
            assert(tpcf_pair_ok(self.reqs@, self.rsps@, k as int));

            // Interference point: participants answer while we are blocked.
            let m = self.rsps[k].recv();

            proof {
                assert(is_rsp(rsp_chan(k as int), k as int));
                assert forall|j: int| 0 <= j < n_parts()
                    implies #[trigger] tpcf_pair_ok(self.reqs@, self.rsps@, j) by {
                    assert(tpcf_pair_ok(self.reqs@, s0, j));
                    if j != k as int { assert(self.rsps@[j] == s0[j]); }
                }
            }

            match m {
                FMsg::Vote(b) => { if !b { all_yes = false; } }
                _ => { all_yes = false; }
            }
            k = k + 1;
        }

        all_yes
    }
}

impl Process for Coordinator {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { self.committed = self.run_round(); }
}
}
