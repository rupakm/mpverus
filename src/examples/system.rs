// Assembling a running system.
//
// Every other example in this directory verifies a *component* under
// preconditions: that it holds a state machine instance, that it holds the
// token for a particular channel, that its endpoints name the channels it
// expects. Nothing in those files discharges those preconditions, and a
// component verified under assumptions nobody establishes proves very little.
// If two components' preconditions were jointly unsatisfiable, each would still
// verify on its own.
//
// This module is the missing wiring, and it is the answer to three questions
// the component files leave open.
//
//   Where does the state machine instance come from?
//       From `Instance::boot`, called once, here.
//
//   Where do the tokens come from?
//       From the same call. `boot` returns the instance together with every
//       token in the system: one per channel for the send histories, one per
//       channel for the consumption records, and the (empty) set of witnesses.
//       No token is created anywhere else, except by `mint`, which creates a
//       channel and its two tokens together.
//
//   How do the tokens reach the threads that need them?
//       By being moved. The map of send tokens is divided by removing the
//       entries a participant needs; what remains belongs to the coordinator.
//       Because a token cannot be copied, this division is exhaustive and
//       disjoint by construction, which is what makes the components'
//       ownership assumptions simultaneously true.
//
// The deployment is of arbitrary size. Its size is fixed by the length of the
// vector of participants' decisions passed to `deploy`, and the channels, the
// token division and the threads are all produced by one loop.

use vstd::prelude::*;
use vstd::tokens::{MapToken, KeyValueToken};
use crate::tok::*;
use crate::proc::*;
use crate::examples::twophase_fanout::*;

verus! {

/// The channels of a deployment with `k` participants: a request channel and a
/// reply channel for each. Defined by recursion so that a deployment of any
/// size can be described, and finite by construction.
pub open spec fn chans_upto(k: int) -> Set<ChanId>
    decreases k
{
    if k <= 0 {
        Set::empty()
    } else {
        chans_upto(k - 1).insert(req_chan(k - 1)).insert(rsp_chan(k - 1))
    }
}

/// The deployment's channels are all named with one index, so none of them is
/// one the allocator could produce. This is what `boot` requires.
pub proof fn lemma_no_dyn(k: int)
    ensures
        forall|f: nat, j: int, i: nat| !chans_upto(k).contains(#[trigger] dyn_chan(f, j, i)),
    decreases k
{
    if k > 0 { lemma_no_dyn(k - 1); }
    assert forall|f: nat, j: int, i: nat|
        !chans_upto(k).contains(#[trigger] dyn_chan(f, j, i)) by {
        assert(!(seq![j, i as int] =~= seq![j]));
        lemma_chan_distinct(f, seq![j, i as int], 0, seq![j]);
        lemma_chan_distinct(f, seq![j, i as int], 1, seq![j]);
    }
}

/// Every participant's two channels are in the set.
pub proof fn lemma_chans_upto(k: int, j: int)
    requires
        0 <= j < k,
    ensures
        chans_upto(k).contains(req_chan(j)),
        chans_upto(k).contains(rsp_chan(j)),
    decreases k
{
    if j < k - 1 {
        lemma_chans_upto(k - 1, j);
    }
}

/// Build the system, run it, and report the outcome.
///
/// `votes` supplies each participant's decision, which the protocol treats as
/// fixed and unknown to the coordinator. Its length fixes the size of the
/// deployment.
///
/// The postcondition is the protocol's safety property, stated about a system
/// that exists rather than about a component in isolation.
pub fn deploy(votes: &Vec<bool>) -> (committed: bool)
    requires
        votes.len() as int == n_parts(),
        n_parts() > 0,
        forall|j: int| 0 <= j < n_parts() ==> #[trigger] votes[j] == vote(j),
    ensures
        committed ==> forall|j: int| 0 <= j < n_parts() ==> vote(j),
{
    proof { config(); }
    let n = votes.len();

    // ---- 1. Create the system's state. This is the only place an instance or
    // a token comes into existence.
    let tracked inst;
    let tracked mut sent_map;
    let tracked mut recvd_map;
    proof {
        lemma_no_dyn(n as int);
        let tracked (i, sm, rm, _witnesses, _next) =
            <NetSM::Instance<FMsg, TpcfTok>>::boot(chans_upto(n as int));
        inst = i.get();
        sent_map = sm.get();
        recvd_map = rm.get();
        assert forall|j: int| 0 <= j < n_parts()
            implies sent_map.dom().contains(#[trigger] req_chan(j)) by {
            lemma_chans_upto(n as int, j);
        }
        assert forall|j: int| 0 <= j < n_parts()
            implies sent_map.dom().contains(#[trigger] rsp_chan(j)) by {
            lemma_chans_upto(n as int, j);
        }
        assert forall|j: int| 0 <= j < n_parts()
            implies recvd_map.dom().contains(#[trigger] req_chan(j)) by {
            lemma_chans_upto(n as int, j);
        }
        assert forall|j: int| 0 <= j < n_parts()
            implies recvd_map.dom().contains(#[trigger] rsp_chan(j)) by {
            lemma_chans_upto(n as int, j);
        }
    }
    let ghost iid = inst.id();

    // ---- 2. For each participant: open its two channels, build the service
    // that owns one end of each, and start it. The coordinator's endpoints
    // accumulate; the participant's move into the thread with its service.
    let mut reqs: Vec<Out<FMsg, TpcfTok>> = Vec::new();
    let mut rsps: Vec<In<FMsg, TpcfTok>> = Vec::new();
    let mut handles: Vec<vstd::thread::JoinHandle<()>> = Vec::new();

    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            n == votes.len(),
            n as int == n_parts(),
            forall|k: int| 0 <= k < n_parts() ==> #[trigger] votes[k] == vote(k),
            reqs.len() == j,
            rsps.len() == j,
            handles.len() == j,
            inst.id() == iid,
            sent_map.instance_id()  == iid,
            recvd_map.instance_id() == iid,
            // the coordinator's endpoints, so far
            forall|k: int| 0 <= k < j ==> #[trigger] tpcf_pair_ok(reqs@, rsps@, k),
            forall|k: int| 0 <= k < j ==> (#[trigger] reqs@[k]).iid() == iid,
            forall|k: int| 0 <= k < j ==> (#[trigger] rsps@[k]).iid() == iid,
            // every channel not yet opened still has both of its tokens
            forall|k: int| j <= k < n_parts()
                ==> sent_map.dom().contains(#[trigger] req_chan(k)),
            forall|k: int| j <= k < n_parts()
                ==> sent_map.dom().contains(#[trigger] rsp_chan(k)),
            forall|k: int| j <= k < n_parts()
                ==> recvd_map.dom().contains(#[trigger] req_chan(k)),
            forall|k: int| j <= k < n_parts()
                ==> recvd_map.dom().contains(#[trigger] rsp_chan(k)),
        decreases n - j,
    {
        proof { config(); }

        // Take BOTH tokens of each channel. Opening a channel consumes them,
        // which is what makes it possible exactly once.
        let tracked cs; let tracked pr; let tracked ps; let tracked cr;
        proof {
            cs = sent_map.remove(req_chan(j as int));
            pr = recvd_map.remove(req_chan(j as int));
            ps = sent_map.remove(rsp_chan(j as int));
            cr = recvd_map.remove(rsp_chan(j as int));
        }

        // The coordinator keeps the request sender and the reply receiver; the
        // participant gets the other end of each.
        let (req_out, req_in) = open_channel::<FMsg, TpcfTok>(
            Ghost(req_chan(j as int)), Tracked(&inst), Tracked(cs), Tracked(pr));
        let (rsp_out, rsp_in) = open_channel::<FMsg, TpcfTok>(
            Ghost(rsp_chan(j as int)), Tracked(&inst), Tracked(ps), Tracked(cr));

        // The participant IS its service. Nothing else is handed over.
        let v = votes[j];
        let p = Participant { j, req: req_in, rsp: rsp_out, my_vote: v };
        let h = vstd::thread::spawn(move ||
            requires p.wf(),
            { let mut p = p; p.step(); });

        let ghost old_reqs = reqs@;
        let ghost old_rsps = rsps@;
        let ghost ro = req_out;
        let ghost ri = rsp_in;
        reqs.push(req_out);
        rsps.push(rsp_in);
        handles.push(h);

        proof {
            assert(reqs@[j as int] == ro);
            assert(rsps@[j as int] == ri);
            assert(ro.wf() && ro.id() == req_chan(j as int));
            assert(ri.wf() && ri.id() == rsp_chan(j as int));
            assert(tpcf_pair_ok(reqs@, rsps@, j as int));
            assert forall|k: int| 0 <= k < j + 1
                implies #[trigger] tpcf_pair_ok(reqs@, rsps@, k) by {
                if k < j {
                    assert(reqs@[k] == old_reqs[k]);
                    assert(rsps@[k] == old_rsps[k]);
                    assert(tpcf_pair_ok(old_reqs, old_rsps, k));
                }
            }
            assert forall|k: int| 0 <= k < j + 1
                implies (#[trigger] reqs@[k]).iid() == iid by { if k < j { } }
            assert forall|k: int| 0 <= k < j + 1
                implies (#[trigger] rsps@[k]).iid() == iid by { if k < j { } }
            assert forall|k: int| j + 1 <= k < n_parts()
                implies sent_map.dom().contains(#[trigger] req_chan(k)) by {
                assert(req_chan(k) != req_chan(j as int));
                assert(req_chan(k) != rsp_chan(j as int));
            }
            assert forall|k: int| j + 1 <= k < n_parts()
                implies sent_map.dom().contains(#[trigger] rsp_chan(k)) by {
                assert(rsp_chan(k) != req_chan(j as int));
                assert(rsp_chan(k) != rsp_chan(j as int));
            }
            assert forall|k: int| j + 1 <= k < n_parts()
                implies recvd_map.dom().contains(#[trigger] req_chan(k)) by {
                assert(req_chan(k) != req_chan(j as int));
                assert(req_chan(k) != rsp_chan(j as int));
            }
            assert forall|k: int| j + 1 <= k < n_parts()
                implies recvd_map.dom().contains(#[trigger] rsp_chan(k)) by {
                assert(rsp_chan(k) != req_chan(j as int));
                assert(rsp_chan(k) != rsp_chan(j as int));
            }
        }
        j = j + 1;
    }

    // ---- 3. Run the coordinator on this thread, over the endpoints that were
    // not given away. Its precondition is now discharged by construction.
    let mut coord = Coordinator { reqs, rsps, committed: false };
    let committed = coord.run_round();

    // ---- 4. Wait for the participants. Their services go with them; the
    // system is shutting down and nothing more will be sent.
    while handles.len() > 0
        decreases handles.len(),
    {
        match handles.pop() {
            Some(hh) => { let _ = hh.join(); }
            None => { }
        }
    }

    committed
}

} // verus!
