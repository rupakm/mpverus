// Standing up a three-acceptor Paxos and running it.
//
// The point is not that the protocol is correct -- `paxos.rs` proves that --
// but that the services proved correct there are the ones that run, and that
// they still finish a round when one acceptor never starts. That second half
// is what `Inbox::collect` was added for: a proposer that waited on acceptors
// one at a time would stop on the first silent one, and no amount of proof
// would fix it, because the dependency is in the control flow.
use vstd::prelude::*;
use vstd::tokens::MapToken;
use crate::tok::*;
use crate::proc::*;
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
/// two indices, and every channel here uses one or three. This is what `boot`
/// requires.
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

/// Two channels of the same family with different acceptor indices are
/// different channels. Removing sixteen tokens from one map needs this.
pub proof fn lemma_px_names(i: int, j: int)
    requires i != j,
    ensures
        alog(i) != alog(j),
        p1a(0, i) != p1a(0, j),
        p1b(0, i) != p1b(0, j),
        p2a(0, i) != p2a(0, j),
        p2b(0, i) != p2b(0, j),
{
    assert(seq![i][0] == i);
    assert(seq![j][0] == j);
    assert(seq![0int, i, 0int][1] == i);
    assert(seq![0int, j, 0int][1] == j);
    lemma_chan_distinct(5, seq![i], 5, seq![j]);
    lemma_chan_distinct(1, seq![0int, i, 0int], 1, seq![0int, j, 0int]);
    lemma_chan_distinct(2, seq![0int, i, 0int], 2, seq![0int, j, 0int]);
    lemma_chan_distinct(3, seq![0int, i, 0int], 3, seq![0int, j, 0int]);
    lemma_chan_distinct(4, seq![0int, i, 0int], 4, seq![0int, j, 0int]);
}


// ---------------------------------------------------------------------------
// Two proposers
// ---------------------------------------------------------------------------
//
// The acceptor above serves whichever proposer speaks, because its inbound
// channels are slots of one mailbox rather than endpoints it chooses between.
// This deployment is where that matters: there are two proposers' worth of
// channels, and the one that never starts is proposer 0 -- the FIRST slot of
// every acceptor's mailbox. An acceptor that received for itself would have to
// name a slot to block on, and naming slot 0 would stop it forever while
// proposer 1 was talking to it.
//
// Only one proposer runs. Two proposers running concurrently is a liveness
// question, not a safety one: duelling proposers can keep raising ballots past
// each other and neither ever gathers a quorum, so a demonstration that has to
// terminate cannot have both live. Safety holds either way -- that is
// `lemma_agreement`, which quantifies over all ballots and all proposers.

pub open spec fn px2_chans() -> Set<ChanId> {
    Set::empty()
        .insert(pdec(1))
        .insert(alog(0))
        .insert(alog(1))
        .insert(alog(2))
        .insert(p1a(0, 0))
        .insert(p1a(0, 1))
        .insert(p1a(0, 2))
        .insert(p1a(1, 0))
        .insert(p1a(1, 1))
        .insert(p1a(1, 2))
        .insert(p1b(0, 0))
        .insert(p1b(0, 1))
        .insert(p1b(0, 2))
        .insert(p1b(1, 0))
        .insert(p1b(1, 1))
        .insert(p1b(1, 2))
        .insert(p2a(0, 0))
        .insert(p2a(0, 1))
        .insert(p2a(0, 2))
        .insert(p2a(1, 0))
        .insert(p2a(1, 1))
        .insert(p2a(1, 2))
        .insert(p2b(0, 0))
        .insert(p2b(0, 1))
        .insert(p2b(0, 2))
        .insert(p2b(1, 0))
        .insert(p2b(1, 1))
        .insert(p2b(1, 2))
}

pub proof fn lemma_px2_no_dyn()
    ensures
        forall|f: nat, j: int, i: nat| !px2_chans().contains(#[trigger] dyn_chan(f, j, i)),
{
    assert forall|f: nat, j: int, i: nat|
        !px2_chans().contains(#[trigger] dyn_chan(f, j, i)) by {
        assert(dyn_chan(f, j, i).ix.len() == 2);
        assert(pdec(1).ix.len() == 1);
        assert(alog(0).ix.len() == 1);
        assert(alog(1).ix.len() == 1);
        assert(alog(2).ix.len() == 1);
        assert(p1a(0, 0).ix.len() == 3);
        assert(p1a(0, 1).ix.len() == 3);
        assert(p1a(0, 2).ix.len() == 3);
        assert(p1a(1, 0).ix.len() == 3);
        assert(p1a(1, 1).ix.len() == 3);
        assert(p1a(1, 2).ix.len() == 3);
        assert(p1b(0, 0).ix.len() == 3);
        assert(p1b(0, 1).ix.len() == 3);
        assert(p1b(0, 2).ix.len() == 3);
        assert(p1b(1, 0).ix.len() == 3);
        assert(p1b(1, 1).ix.len() == 3);
        assert(p1b(1, 2).ix.len() == 3);
        assert(p2a(0, 0).ix.len() == 3);
        assert(p2a(0, 1).ix.len() == 3);
        assert(p2a(0, 2).ix.len() == 3);
        assert(p2a(1, 0).ix.len() == 3);
        assert(p2a(1, 1).ix.len() == 3);
        assert(p2a(1, 2).ix.len() == 3);
        assert(p2b(0, 0).ix.len() == 3);
        assert(p2b(0, 1).ix.len() == 3);
        assert(p2b(0, 2).ix.len() == 3);
        assert(p2b(1, 0).ix.len() == 3);
        assert(p2b(1, 1).ix.len() == 3);
        assert(p2b(1, 2).ix.len() == 3);
    }
}

/// Two pair channels of the same family are different unless they name the
/// same proposer AND the same acceptor.
pub proof fn lemma_pair_names(p1: int, a1: int, p2: int, a2: int)
    requires p1 != p2 || a1 != a2,
    ensures
        p1a(p1, a1) != p1a(p2, a2),
        p1b(p1, a1) != p1b(p2, a2),
        p2a(p1, a1) != p2a(p2, a2),
        p2b(p1, a1) != p2b(p2, a2),
{
    assert(seq![p1, a1, 0][0] == p1);
    assert(seq![p1, a1, 0][1] == a1);
    assert(seq![p2, a2, 0][0] == p2);
    assert(seq![p2, a2, 0][1] == a2);
    lemma_chan_distinct(1, seq![p1, a1, 0], 1, seq![p2, a2, 0]);
    lemma_chan_distinct(2, seq![p1, a1, 0], 2, seq![p2, a2, 0]);
    lemma_chan_distinct(3, seq![p1, a1, 0], 3, seq![p2, a2, 0]);
    lemma_chan_distinct(4, seq![p1, a1, 0], 4, seq![p2, a2, 0]);
}

/// Boot a three-acceptor Paxos, run `rounds` rounds, and report the value
/// committed by the last one.
///
/// `live` acceptors are started; the rest are built and dropped. With `live`
/// two, one acceptor never reads its channels and never answers, and the round
/// still completes on the quorum that does.
///
/// After the first round the proposer's preferred value changes, so a second
/// round exercises the part of phase one that matters: a quorum reports what it
/// already accepted, and the proposer must take the highest report rather than
/// what it wanted.
pub fn deploy_paxos(live: usize, rounds: usize) -> (v: u64)
    requires 2 <= live <= 3, 1 <= rounds <= 8,
{
    proof { px_config(); }

    let tracked inst;
    let tracked mut sm;
    let tracked mut rm;
    proof {
        lemma_px_no_dyn();
        let tracked (i, s, r, _w, _n) = <NetSM::Instance<PMsg, Paxos>>::boot(px_chans());
        inst = i.get(); sm = s.get(); rm = r.get();
    }

    proof {
        lemma_px_names(0, 1); lemma_px_names(0, 2); lemma_px_names(1, 2);
    }

    // The sixteen channels.
    let (dec_out, _dec_in) = take_channel::<PMsg, Paxos>(
        Ghost(pdec(0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    let (al0_out, _al0_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (al1_out, _al1_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (al2_out, _al2_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    let (q1a0_out, q1a0_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q1a1_out, q1a1_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q1a2_out, q1a2_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    let (q1b0_out, q1b0_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q1b1_out, q1b1_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q1b2_out, q1b2_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    let (q2a0_out, q2a0_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q2a1_out, q2a1_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q2a2_out, q2a2_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    let (q2b0_out, _q2b0_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q2b1_out, _q2b1_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (q2b2_out, _q2b2_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    // The three acceptors. Each names one proposer, so every vector has one
    // slot; the shapes are what `Acceptor::inv` asks for.
    let acc0 = build_acceptor(0, Tracked(inst.clone()), q1a0_in, q1b0_out,
                              q2a0_in, q2b0_out, al0_out);
    let acc1 = build_acceptor(1, Tracked(inst.clone()), q1a1_in, q1b1_out,
                              q2a1_in, q2b1_out, al1_out);
    let acc2 = build_acceptor(2, Tracked(inst.clone()), q1a2_in, q1b2_out,
                              q2a2_in, q2b2_out, al2_out);

    // The proposer. Promises arrive on a mailbox, so phase one takes whichever
    // two answer first.
    let mut preps = FanOut::<PMsg, Paxos>::new();
    preps.add(q1a0_out); preps.add(q1a1_out); preps.add(q1a2_out);
    let mut accs = FanOut::<PMsg, Paxos>::new();
    accs.add(q2a0_out); accs.add(q2a1_out); accs.add(q2a2_out);

    let tracked ip = inst.clone();
    let mut promises = Inbox::<PMsg, Paxos>::empty(Tracked(ip));
    promises.add(q1b0_in);
    promises.add(q1b1_in);
    promises.add(q1b2_in);
    let mut prop = Proposer {
        id: 0,
        prepares: preps,
        promises,
        accepts:  accs,
        log: dec_out,
        // Above the acceptors' initial ballot, so phase one is not refused.
        bal: Ballot { round: 1, prop: 0 },
        want: 42,
    };
    assert(prop.inv()) by {
        assert(prop.prepares.ids@ =~= Seq::new(3nat, |a: int| p1a(0, a)));
        assert(prop.accepts.ids@  =~= Seq::new(3nat, |a: int| p2a(0, a)));
    }

    let h0 = vstd::thread::spawn(move ||
        requires acc0.inv(),
        { let mut a = acc0; run(&mut a, 2 * rounds); });
    let h1 = vstd::thread::spawn(move ||
        requires acc1.inv(),
        { let mut a = acc1; run(&mut a, 2 * rounds); });

    // The third acceptor runs only if this deployment says it is up. When it
    // is not, it is built and dropped: its channels exist and the proposer
    // still writes to them, but nobody ever reads.
    let h2 = if live == 3 {
        Some(vstd::thread::spawn(move ||
            requires acc2.inv(),
            { let mut a = acc2; run(&mut a, 2 * rounds); }))
    } else {
        None
    };

    let mut v: u64 = 0;
    let mut i: usize = 0;
    while i < rounds
        invariant
            0 <= i <= rounds, rounds <= 8,
            prop.inv(), prop.bal.round == i + 1,
        decreases rounds - i,
    {
        // What this proposer would pick if phase one leaves it free. Only the
        // first round is free; after that a quorum has accepted something.
        if i > 0 { prop.want = 99; }
        v = prop.round();
        i = i + 1;
    }

    match (h0.join(), h1.join()) {
        (Ok(_), Ok(_)) => { }
        _ => { abort_on_panicked_child() }
    }
    match h2 {
        Some(h) => match h.join() {
            Ok(_) => { }
            _ => { abort_on_panicked_child() }
        },
        None => { }
    }
    v
}


/// All fifteen pairs of (proposer, acceptor) this deployment uses.
pub proof fn lemma_all_pair_names()
    ensures
        p1a(0, 0) != p1a(0, 1), p1b(0, 0) != p1b(0, 1),
        p2a(0, 0) != p2a(0, 1), p2b(0, 0) != p2b(0, 1),
        p1a(0, 0) != p1a(0, 2), p1b(0, 0) != p1b(0, 2),
        p2a(0, 0) != p2a(0, 2), p2b(0, 0) != p2b(0, 2),
        p1a(0, 0) != p1a(1, 0), p1b(0, 0) != p1b(1, 0),
        p2a(0, 0) != p2a(1, 0), p2b(0, 0) != p2b(1, 0),
        p1a(0, 0) != p1a(1, 1), p1b(0, 0) != p1b(1, 1),
        p2a(0, 0) != p2a(1, 1), p2b(0, 0) != p2b(1, 1),
        p1a(0, 0) != p1a(1, 2), p1b(0, 0) != p1b(1, 2),
        p2a(0, 0) != p2a(1, 2), p2b(0, 0) != p2b(1, 2),
        p1a(0, 1) != p1a(0, 2), p1b(0, 1) != p1b(0, 2),
        p2a(0, 1) != p2a(0, 2), p2b(0, 1) != p2b(0, 2),
        p1a(0, 1) != p1a(1, 0), p1b(0, 1) != p1b(1, 0),
        p2a(0, 1) != p2a(1, 0), p2b(0, 1) != p2b(1, 0),
        p1a(0, 1) != p1a(1, 1), p1b(0, 1) != p1b(1, 1),
        p2a(0, 1) != p2a(1, 1), p2b(0, 1) != p2b(1, 1),
        p1a(0, 1) != p1a(1, 2), p1b(0, 1) != p1b(1, 2),
        p2a(0, 1) != p2a(1, 2), p2b(0, 1) != p2b(1, 2),
        p1a(0, 2) != p1a(1, 0), p1b(0, 2) != p1b(1, 0),
        p2a(0, 2) != p2a(1, 0), p2b(0, 2) != p2b(1, 0),
        p1a(0, 2) != p1a(1, 1), p1b(0, 2) != p1b(1, 1),
        p2a(0, 2) != p2a(1, 1), p2b(0, 2) != p2b(1, 1),
        p1a(0, 2) != p1a(1, 2), p1b(0, 2) != p1b(1, 2),
        p2a(0, 2) != p2a(1, 2), p2b(0, 2) != p2b(1, 2),
        p1a(1, 0) != p1a(1, 1), p1b(1, 0) != p1b(1, 1),
        p2a(1, 0) != p2a(1, 1), p2b(1, 0) != p2b(1, 1),
        p1a(1, 0) != p1a(1, 2), p1b(1, 0) != p1b(1, 2),
        p2a(1, 0) != p2a(1, 2), p2b(1, 0) != p2b(1, 2),
        p1a(1, 1) != p1a(1, 2), p1b(1, 1) != p1b(1, 2),
        p2a(1, 1) != p2a(1, 2), p2b(1, 1) != p2b(1, 2),
{
    lemma_pair_names(0, 0, 0, 1);
    lemma_pair_names(0, 0, 0, 2);
    lemma_pair_names(0, 0, 1, 0);
    lemma_pair_names(0, 0, 1, 1);
    lemma_pair_names(0, 0, 1, 2);
    lemma_pair_names(0, 1, 0, 2);
    lemma_pair_names(0, 1, 1, 0);
    lemma_pair_names(0, 1, 1, 1);
    lemma_pair_names(0, 1, 1, 2);
    lemma_pair_names(0, 2, 1, 0);
    lemma_pair_names(0, 2, 1, 1);
    lemma_pair_names(0, 2, 1, 2);
    lemma_pair_names(1, 0, 1, 1);
    lemma_pair_names(1, 0, 1, 2);
    lemma_pair_names(1, 1, 1, 2);
}

/// Boot three acceptors that each know TWO proposers, and run only the second.
///
/// Proposer 0 never starts, so slot 0 of every acceptor's mailbox -- its
/// `Prepare` channel -- stays silent for the whole run. Proposer 1 completes a
/// round anyway. That is the property `NetHandler` buys: the acceptor never
/// names a peer to wait for.
pub fn deploy_paxos_two(live: usize) -> (v: u64)
    requires 2 <= live <= 3,
{
    proof { px_config(); }

    let tracked inst;
    let tracked mut sm;
    let tracked mut rm;
    proof {
        lemma_px2_no_dyn();
        let tracked (i, s, r, _w, _n) = <NetSM::Instance<PMsg, Paxos>>::boot(px2_chans());
        inst = i.get(); sm = s.get(); rm = r.get();
    }

    proof {
        lemma_all_pair_names();
        lemma_px_names(0, 1); lemma_px_names(0, 2); lemma_px_names(1, 2);
    }

    let (dec_out, _dec_in) = take_channel::<PMsg, Paxos>(
        Ghost(pdec(1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (al0_out, _al0_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (al1_out, _al1_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (al2_out, _al2_in) = take_channel::<PMsg, Paxos>(
        Ghost(alog(2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    proof { lemma_all_pair_names(); }
    let (p1a_00_out, p1a_00_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1a_01_out, p1a_01_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1a_02_out, p1a_02_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1a_10_out, p1a_10_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(1, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1a_11_out, p1a_11_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(1, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1a_12_out, p1a_12_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1a(1, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    proof { lemma_all_pair_names(); }
    let (p1b_00_out, p1b_00_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1b_01_out, p1b_01_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1b_02_out, p1b_02_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1b_10_out, p1b_10_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(1, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1b_11_out, p1b_11_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(1, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p1b_12_out, p1b_12_in) = take_channel::<PMsg, Paxos>(
        Ghost(p1b(1, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    proof { lemma_all_pair_names(); }
    let (p2a_00_out, p2a_00_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2a_01_out, p2a_01_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2a_02_out, p2a_02_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2a_10_out, p2a_10_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(1, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2a_11_out, p2a_11_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(1, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2a_12_out, p2a_12_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2a(1, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    proof { lemma_all_pair_names(); }
    let (p2b_00_out, p2b_00_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2b_01_out, p2b_01_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2b_02_out, p2b_02_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2b_10_out, p2b_10_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(1, 0)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2b_11_out, p2b_11_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(1, 1)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));
    let (p2b_12_out, p2b_12_in) = take_channel::<PMsg, Paxos>(
        Ghost(p2b(1, 2)), Tracked(&inst), Tracked(&mut sm), Tracked(&mut rm));

    // Three acceptors, each with a two-slot-per-phase mailbox.
    let acc0 = build_acceptor2(0, Tracked(inst.clone()),
        p1a_00_in, p1a_10_in, p1b_00_out, p1b_10_out,
        p2a_00_in, p2a_10_in, p2b_00_out, p2b_10_out, al0_out);
    let acc1 = build_acceptor2(1, Tracked(inst.clone()),
        p1a_01_in, p1a_11_in, p1b_01_out, p1b_11_out,
        p2a_01_in, p2a_11_in, p2b_01_out, p2b_11_out, al1_out);
    let acc2 = build_acceptor2(2, Tracked(inst.clone()),
        p1a_02_in, p1a_12_in, p1b_02_out, p1b_12_out,
        p2a_02_in, p2a_12_in, p2b_02_out, p2b_12_out, al2_out);

    // Proposer 1. Proposer 0's endpoints are opened and dropped: its channels
    // exist, the acceptors listen on them, and nothing ever arrives.
    let mut preps = FanOut::<PMsg, Paxos>::new();
    preps.add(p1a_10_out); preps.add(p1a_11_out); preps.add(p1a_12_out);
    let mut accs = FanOut::<PMsg, Paxos>::new();
    accs.add(p2a_10_out); accs.add(p2a_11_out); accs.add(p2a_12_out);

    let tracked ip = inst.clone();
    let mut promises = Inbox::<PMsg, Paxos>::empty(Tracked(ip));
    promises.add(p1b_10_in);
    promises.add(p1b_11_in);
    promises.add(p1b_12_in);

    let mut prop = Proposer {
        id: 1,
        prepares: preps,
        promises,
        accepts: accs,
        log: dec_out,
        bal: Ballot { round: 1, prop: 1 },
        want: 7,
    };
    assert(prop.inv()) by {
        assert(prop.prepares.ids@ =~= Seq::new(3nat, |a: int| p1a(1, a)));
        assert(prop.accepts.ids@  =~= Seq::new(3nat, |a: int| p2a(1, a)));
        assert(prop.promises.ids@ =~= Seq::new(3nat, |a: int| p1b(1, a)));
    }

    let h0 = vstd::thread::spawn(move ||
        requires acc0.inv(),
        { let mut a = acc0; run(&mut a, 2); });
    let h1 = vstd::thread::spawn(move ||
        requires acc1.inv(),
        { let mut a = acc1; run(&mut a, 2); });
    let h2 = if live == 3 {
        Some(vstd::thread::spawn(move ||
            requires acc2.inv(),
            { let mut a = acc2; run(&mut a, 2); }))
    } else {
        None
    };

    let v = prop.round();

    match (h0.join(), h1.join()) {
        (Ok(_), Ok(_)) => { }
        _ => { abort_on_panicked_child() }
    }
    match h2 {
        Some(h) => match h.join() {
            Ok(_) => { }
            _ => { abort_on_panicked_child() }
        },
        None => { }
    }
    v
}

/// One acceptor that knows two proposers. Mailbox order is `chans`: every
/// `Prepare` channel, then every `Accept` channel.
fn build_acceptor2(
    id: usize,
    Tracked(inst): Tracked<NetSM::Instance<PMsg, Paxos>>,
    prep0: In<PMsg, Paxos>, prep1: In<PMsg, Paxos>,
    prom0: Out<PMsg, Paxos>, prom1: Out<PMsg, Paxos>,
    acc0: In<PMsg, Paxos>, acc1: In<PMsg, Paxos>,
    accd0: Out<PMsg, Paxos>, accd1: Out<PMsg, Paxos>,
    log: Out<PMsg, Paxos>,
) -> (d: Driven<PMsg, Paxos, Acceptor>)
    requires
        prep0.wf(), prep0.id() == p1a(0, id as int),
        prep1.wf(), prep1.id() == p1a(1, id as int),
        prom0.wf(), prom0.id() == p1b(0, id as int),
        prom1.wf(), prom1.id() == p1b(1, id as int),
        acc0.wf(),  acc0.id()  == p2a(0, id as int),
        acc1.wf(),  acc1.id()  == p2a(1, id as int),
        accd0.wf(), accd0.id() == p2b(0, id as int),
        accd1.wf(), accd1.id() == p2b(1, id as int),
        log.wf(), log.id() == alog(id as int), log.hist() == Seq::<PMsg>::empty(),
        log.iid() == inst.id(),
        prep0.iid() == inst.id(), prep1.iid() == inst.id(),
        prom0.iid() == inst.id(), prom1.iid() == inst.id(),
        acc0.iid()  == inst.id(), acc1.iid()  == inst.id(),
        accd0.iid() == inst.id(), accd1.iid() == inst.id(),
    ensures d.inv(),
{
    let mut inbox = Inbox::<PMsg, Paxos>::empty(Tracked(inst));
    inbox.add(prep0);
    inbox.add(prep1);
    inbox.add(acc0);
    inbox.add(acc1);

    let mut po = FanOut::<PMsg, Paxos>::new(); po.add(prom0); po.add(prom1);
    let mut ao = FanOut::<PMsg, Paxos>::new(); ao.add(accd0); ao.add(accd1);
    let a = Acceptor {
        id, n_prop: 2,
        promises: po, accepteds: ao,
        log,
        max_bal: Ballot { round: 0, prop: 0 },
        has_acc: false,
        acc_bal: Ballot { round: 0, prop: 0 },
        acc_val: 0,
    };
    assert(a.inv()) by {
        assert(a.promises.ids@  =~= Seq::new(2nat, |p: int| p1b(p, id as int)));
        assert(a.accepteds.ids@ =~= Seq::new(2nat, |p: int| p2b(p, id as int)));
    }
    let d = Driven { h: a, inbox };
    assert(d.inv()) by {
        assert(d.inbox.ids@ =~= d.h.chans());
    }
    d
}

/// One acceptor, wired to the single proposer, ready to be driven.
///
/// The mailbox holds both of its inbound channels, in the order `chans` says:
/// the Prepare channel, then the Accept channel. Which of the two arrives
/// first is not this acceptor's business.
fn build_acceptor(
    id: usize,
    Tracked(inst): Tracked<NetSM::Instance<PMsg, Paxos>>,
    prep_in: In<PMsg, Paxos>,
    prom_out: Out<PMsg, Paxos>,
    acc_in: In<PMsg, Paxos>,
    accd_out: Out<PMsg, Paxos>,
    log: Out<PMsg, Paxos>,
) -> (d: Driven<PMsg, Paxos, Acceptor>)
    requires
        prep_in.wf(),  prep_in.id()  == p1a(0, id as int),
        prom_out.wf(), prom_out.id() == p1b(0, id as int),
        acc_in.wf(),   acc_in.id()   == p2a(0, id as int),
        accd_out.wf(), accd_out.id() == p2b(0, id as int),
        log.wf(),      log.id()      == alog(id as int),
        log.hist() == Seq::<PMsg>::empty(),
        log.iid() == inst.id(),
        prep_in.iid() == inst.id(), prom_out.iid() == inst.id(),
        acc_in.iid()  == inst.id(), accd_out.iid() == inst.id(),
    ensures d.inv(),
{
    let mut inbox = Inbox::<PMsg, Paxos>::empty(Tracked(inst));
    inbox.add(prep_in);
    inbox.add(acc_in);

    let mut po = FanOut::<PMsg, Paxos>::new(); po.add(prom_out);
    let mut ao = FanOut::<PMsg, Paxos>::new(); ao.add(accd_out);
    let a = Acceptor {
        id, n_prop: 1,
        promises: po, accepteds: ao,
        log,
        max_bal: Ballot { round: 0, prop: 0 },
        has_acc: false,
        acc_bal: Ballot { round: 0, prop: 0 },
        acc_val: 0,
    };
    assert(a.inv()) by {
        assert(a.promises.ids@  =~= Seq::new(1nat, |p: int| p1b(p, id as int)));
        assert(a.accepteds.ids@ =~= Seq::new(1nat, |p: int| p2b(p, id as int)));
    }
    let d = Driven { h: a, inbox };
    assert(d.inv()) by {
        assert(d.inbox.ids@ =~= d.h.chans());
    }
    d
}

} // verus!
