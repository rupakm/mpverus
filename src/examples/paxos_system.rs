// Standing up a three-acceptor Paxos and running it.
//
// The point is not that the protocol is correct -- `paxos.rs` proves that -- but
// that the services proved correct there are the ones that run, and that they
// still make progress when the network does not cooperate.
use vstd::prelude::*;
use vstd::tokens::{MapToken, SetToken};
use crate::tok::*;
use crate::proc::*;
use crate::quorum::*;
use crate::examples::paxos::*;

verus! {

/// This deployment has three acceptors and one proposer. A quorum is two.
#[verifier::external_body]
pub proof fn px_config()
    ensures n_acc() == 3,
{
}

/// Every channel of the deployment: the proposer's log, each acceptor's log,
/// and the four per-pair channels.
pub open spec fn px_chans() -> Set<ChanId> {
    Set::empty()
        .insert(pdec(0))
        .insert(alog(0)).insert(alog(1)).insert(alog(2))
        .insert(p1a(0, 0)).insert(p1a(0, 1)).insert(p1a(0, 2))
        .insert(p1b(0, 0)).insert(p1b(0, 1)).insert(p1b(0, 2))
        .insert(p2a(0, 0)).insert(p2a(0, 1)).insert(p2a(0, 2))
        .insert(p2b(0, 0)).insert(p2b(0, 1)).insert(p2b(0, 2))
}

/// None of them is a name the allocator could produce: `dyn_chan` uses exactly
/// two indices, and every channel here uses one or three.
pub proof fn lemma_px_no_dyn()
    ensures
        forall|f: nat, j: int, i: nat| !px_chans().contains(#[trigger] dyn_chan(f, j, i)),
{
    assert forall|f: nat, j: int, i: nat|
        !px_chans().contains(#[trigger] dyn_chan(f, j, i)) by {
        assert(dyn_chan(f, j, i).ix.len() == 2);
        assert(pdec(0).ix.len() == 1);
        assert(alog(0).ix.len() == 1);
        assert(alog(1).ix.len() == 1);
        assert(alog(2).ix.len() == 1);
        assert(p1a(0, 0).ix.len() == 3);
        assert(p1a(0, 1).ix.len() == 3);
        assert(p1a(0, 2).ix.len() == 3);
        assert(p1b(0, 0).ix.len() == 3);
        assert(p1b(0, 1).ix.len() == 3);
        assert(p1b(0, 2).ix.len() == 3);
        assert(p2a(0, 0).ix.len() == 3);
        assert(p2a(0, 1).ix.len() == 3);
        assert(p2a(0, 2).ix.len() == 3);
        assert(p2b(0, 0).ix.len() == 3);
        assert(p2b(0, 1).ix.len() == 3);
        assert(p2b(0, 2).ix.len() == 3);
    }
}

} // verus!
