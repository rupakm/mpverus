// Assembling and RUNNING the lease lock.
//
// `system.rs` shows where an instance and its tokens come from and how they
// reach the threads that need them. This module does the same for the lease
// lock and then actually runs it, which is a different claim: that the source
// Verus checks is the source that executes.
//
// The lease lock is the right protocol for that. It has no uninterpreted
// parameters, so a deployment needs no configuration axiom, and it exercises
// three kinds of service, a mailbox over many peers, and provenance.
use vstd::prelude::*;
use vstd::tokens::MapToken;
use crate::tok::*;
use crate::proc::*;
use crate::examples::leaselock::*;

verus! {

/// The channels of a deployment with `k` writers: four per writer, plus the
/// journal. Defined by recursion, so a deployment of any size is describable
/// and the set is finite by construction.
pub open spec fn ll_chans(k: int) -> Set<ChanId>
    decreases k
{
    if k <= 0 {
        Set::empty().insert(journal())
    } else {
        ll_chans(k - 1)
            .insert(acq_req(k - 1)).insert(acq_rsp(k - 1))
            .insert(wr_req(k - 1)).insert(wr_rsp(k - 1))
    }
}

/// None of these names has two indices, so none is one the allocator could
/// produce. This is what `boot` requires.
pub proof fn lemma_ll_no_dyn(k: int)
    ensures
        forall|f: nat, j: int, i: nat| !ll_chans(k).contains(#[trigger] dyn_chan(f, j, i)),
    decreases k
{
    if k <= 0 {
        assert forall|f: nat, j: int, i: nat|
            !ll_chans(k).contains(#[trigger] dyn_chan(f, j, i)) by {
            lemma_chan_distinct(f, seq![j, i as int], 4, seq![]);
        }
    } else {
        lemma_ll_no_dyn(k - 1);
        assert forall|f: nat, j: int, i: nat|
            !ll_chans(k).contains(#[trigger] dyn_chan(f, j, i)) by {
            lemma_chan_distinct(f, seq![j, i as int], 0, seq![k - 1]);
            lemma_chan_distinct(f, seq![j, i as int], 1, seq![k - 1]);
            lemma_chan_distinct(f, seq![j, i as int], 2, seq![k - 1]);
            lemma_chan_distinct(f, seq![j, i as int], 3, seq![k - 1]);
        }
    }
}

/// Writer `w`'s four channels, and the journal, are in the set.
pub proof fn lemma_ll_chans(k: int, w: int)
    requires 0 <= w < k,
    ensures
        ll_chans(k).contains(acq_req(w)), ll_chans(k).contains(acq_rsp(w)),
        ll_chans(k).contains(wr_req(w)),  ll_chans(k).contains(wr_rsp(w)),
    decreases k
{
    if w == k - 1 { } else { lemma_ll_chans(k - 1, w); }
}

pub proof fn lemma_ll_journal(k: int)
    ensures ll_chans(k).contains(journal()),
    decreases k
{
    if k <= 0 { } else { lemma_ll_journal(k - 1); }
}

/// Boot a lease lock with ONE writer, run it, and report whether the writer's
/// last write was accepted.
///
/// One writer, and straight-line rather than looped, because this exists to be
/// RUN. `system.rs` already shows the arbitrary-size deployment with a loop;
/// what is new here is that the result comes back through the endpoint API of
/// services Verus checked. Two things make more writers awkward, and both are
/// recorded in `plan.md`: the storage node blocks on one writer's channel at a
/// time rather than waiting on all of them, and a terminating demo has to
/// choose step counts that match.
pub fn deploy_lease() -> (accepted: bool)
{
    // ---- 1. The system's state. The only place an instance or token is made.
    let tracked inst;
    let tracked mut sent_map;
    let tracked mut recvd_map;
    proof {
        lemma_ll_no_dyn(1);
        lemma_ll_chans(1, 0);
        lemma_ll_journal(1);
        let tracked (i, sm, rm, _witnesses, _next) =
            <NetSM::Instance<Msg, Lease>>::boot(ll_chans(1));
        inst = i.get();
        sent_map = sm.get();
        recvd_map = rm.get();
    }

    // ---- 2. Open the five channels, taking both tokens of each.
    let (acq_out, acq_in) = take_channel::<Msg, Lease>(
        Ghost(acq_req(0)), Tracked(&inst), Tracked(&mut sent_map), Tracked(&mut recvd_map));
    let (grt_out, grt_in) = take_channel::<Msg, Lease>(
        Ghost(acq_rsp(0)), Tracked(&inst), Tracked(&mut sent_map), Tracked(&mut recvd_map));
    let (wr_out, wr_in) = take_channel::<Msg, Lease>(
        Ghost(wr_req(0)), Tracked(&inst), Tracked(&mut sent_map), Tracked(&mut recvd_map));
    let (ack_out, ack_in) = take_channel::<Msg, Lease>(
        Ghost(wr_rsp(0)), Tracked(&inst), Tracked(&mut sent_map), Tracked(&mut recvd_map));
    let (jrn_out, _jrn_in) = take_channel::<Msg, Lease>(
        Ghost(journal()), Tracked(&inst), Tracked(&mut sent_map), Tracked(&mut recvd_map));

    // ---- 3. Build the three services. Each is handed exactly the ends it owns.
    let tracked i1 = inst.clone();
    let mut srv_inbox = Inbox::<Msg, Lease>::empty(Tracked(i1));
    srv_inbox.add(acq_in);

    let mut srv_rsps = FanOut::<Msg, Lease>::new();
    srv_rsps.add(grt_out);
    let mut server = LockServer {
        inbox: srv_inbox,
        rsps: srv_rsps,
        hi: 0, held: false, held_until: 0,
    };

    let mut st_reqs = FanIn::<Msg, Lease>::new();
    st_reqs.add(wr_in);
    let mut st_rsps = FanOut::<Msg, Lease>::new();
    st_rsps.add(ack_out);
    let mut storage = StorageNode {
        reqs: st_reqs,
        rsps: st_rsps,
        jrn: jrn_out,
        hi_token: 0, hi_seq: 0, have_any: false, turn: 0,
    };

    // The writer's mailbox: slot 0 the grant channel, slot 1 the
    // acknowledgement channel, in the order its `chans()` declares. `Driven`'s
    // invariant is what checks that they match.
    let tracked i2 = inst.clone();
    let mut wr_inbox = Inbox::<Msg, Lease>::empty(Tracked(i2));
    wr_inbox.add(grt_in);
    wr_inbox.add(ack_in);

    let writer = Writer {
        id: 0, acq: acq_out, wr: wr_out,
        token: 0, seq: 0, val: 7, last_ok: false,
        phase: WPhase::Idle,
        lease: Tracked(None),
    };
    let mut driven = Driven {
        h: writer,
        inbox: wr_inbox,
    };
    assert(driven.inv()) by {
        assert(driven.inbox.ids@ =~= driven.h.chans());
    }

    // ---- 4. Run. The counts are chosen so every service finishes: the writer
    // acquires once and then writes four times, so the server serves one
    // request and the storage node handles four.
    let hs = vstd::thread::spawn(move ||
        requires server.wf(),
        { let mut s = server; run(&mut s, 1); });
    let ht = vstd::thread::spawn(move ||
        requires storage.wf(),
        { let mut s = storage; run(&mut s, 4); });

    run(&mut driven, 5);

    match (hs.join(), ht.join()) {
        (Ok(_), Ok(_)) => { }
        _ => { abort_on_panicked_child() }
    }
    driven.h.last_ok
}

} // verus!
