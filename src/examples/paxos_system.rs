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
    let tracked (s, r) = (sm.remove(pdec(0)), rm.remove(pdec(0)));
    let (dec_out, _dec_in) = open_channel::<PMsg, Paxos>(
        Ghost(pdec(0)), Tracked(&inst), Tracked(s), Tracked(r));

    let tracked (s, r) = (sm.remove(alog(0)), rm.remove(alog(0)));
    let (al0_out, _al0_in) = open_channel::<PMsg, Paxos>(
        Ghost(alog(0)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(alog(1)), rm.remove(alog(1)));
    let (al1_out, _al1_in) = open_channel::<PMsg, Paxos>(
        Ghost(alog(1)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(alog(2)), rm.remove(alog(2)));
    let (al2_out, _al2_in) = open_channel::<PMsg, Paxos>(
        Ghost(alog(2)), Tracked(&inst), Tracked(s), Tracked(r));

    let tracked (s, r) = (sm.remove(p1a(0, 0)), rm.remove(p1a(0, 0)));
    let (q1a0_out, q1a0_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 0)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p1a(0, 1)), rm.remove(p1a(0, 1)));
    let (q1a1_out, q1a1_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 1)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p1a(0, 2)), rm.remove(p1a(0, 2)));
    let (q1a2_out, q1a2_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1a(0, 2)), Tracked(&inst), Tracked(s), Tracked(r));

    let tracked (s, r) = (sm.remove(p1b(0, 0)), rm.remove(p1b(0, 0)));
    let (q1b0_out, q1b0_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 0)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p1b(0, 1)), rm.remove(p1b(0, 1)));
    let (q1b1_out, q1b1_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 1)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p1b(0, 2)), rm.remove(p1b(0, 2)));
    let (q1b2_out, q1b2_in) = open_channel::<PMsg, Paxos>(
        Ghost(p1b(0, 2)), Tracked(&inst), Tracked(s), Tracked(r));

    let tracked (s, r) = (sm.remove(p2a(0, 0)), rm.remove(p2a(0, 0)));
    let (q2a0_out, q2a0_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 0)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p2a(0, 1)), rm.remove(p2a(0, 1)));
    let (q2a1_out, q2a1_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 1)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p2a(0, 2)), rm.remove(p2a(0, 2)));
    let (q2a2_out, q2a2_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2a(0, 2)), Tracked(&inst), Tracked(s), Tracked(r));

    let tracked (s, r) = (sm.remove(p2b(0, 0)), rm.remove(p2b(0, 0)));
    let (q2b0_out, _q2b0_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 0)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p2b(0, 1)), rm.remove(p2b(0, 1)));
    let (q2b1_out, _q2b1_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 1)), Tracked(&inst), Tracked(s), Tracked(r));
    let tracked (s, r) = (sm.remove(p2b(0, 2)), rm.remove(p2b(0, 2)));
    let (q2b2_out, _q2b2_in) = open_channel::<PMsg, Paxos>(
        Ghost(p2b(0, 2)), Tracked(&inst), Tracked(s), Tracked(r));

    // The three acceptors. Each names one proposer, so every vector has one
    // slot; the shapes are what `Acceptor::inv` asks for.
    let acc0 = build_acceptor(0, q1a0_in, q1b0_out, q2a0_in, q2b0_out, al0_out);
    let acc1 = build_acceptor(1, q1a1_in, q1b1_out, q2a1_in, q2b1_out, al1_out);
    let acc2 = build_acceptor(2, q1a2_in, q1b2_out, q2a2_in, q2b2_out, al2_out);

    // The proposer. Promises arrive on a mailbox, so phase one takes whichever
    // two answer first.
    let mut preps: Vec<Out<PMsg, Paxos>> = Vec::new();
    preps.push(q1a0_out); preps.push(q1a1_out); preps.push(q1a2_out);
    let mut accs: Vec<Out<PMsg, Paxos>> = Vec::new();
    accs.push(q2a0_out); accs.push(q2a1_out); accs.push(q2a2_out);

    let tracked ip = inst.clone();
    let mut promises = Inbox::<PMsg, Paxos>::empty(Tracked(ip));
    promises.add(q1b0_in);
    promises.add(q1b1_in);
    promises.add(q1b2_in);
    let mut prop = Proposer {
        id: 0,
        prepares: FanOut { outs: preps, ids: Ghost(Seq::new(3nat, |a: int| p1a(0, a))) },
        promises,
        accepts:  FanOut { outs: accs,  ids: Ghost(Seq::new(3nat, |a: int| p2a(0, a))) },
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
        requires acc0.inv() && acc0.np() == 1,
        { serve(acc0, rounds); });
    let h1 = vstd::thread::spawn(move ||
        requires acc1.inv() && acc1.np() == 1,
        { serve(acc1, rounds); });

    // The third acceptor runs only if this deployment says it is up. When it
    // is not, it is built and dropped: its channels exist and the proposer
    // still writes to them, but nobody ever reads.
    let h2 = if live == 3 {
        Some(vstd::thread::spawn(move ||
            requires acc2.inv() && acc2.np() == 1,
            { serve(acc2, rounds); }))
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

/// An acceptor's whole life: answer phase one and phase two, once per round.
fn serve(a: Acceptor, rounds: usize)
    requires a.inv(), a.np() == 1,
{
    let mut a = a;
    let mut i: usize = 0;
    while i < rounds
        invariant a.inv(), a.np() == 1,
        decreases rounds - i,
    {
        a.handle_prepare(0);
        a.handle_accept(0);
        i = i + 1;
    }
}

/// One acceptor, wired to the single proposer.
fn build_acceptor(
    id: usize,
    prep_in: In<PMsg, Paxos>,
    prom_out: Out<PMsg, Paxos>,
    acc_in: In<PMsg, Paxos>,
    accd_out: Out<PMsg, Paxos>,
    log: Out<PMsg, Paxos>,
) -> (a: Acceptor)
    requires
        prep_in.wf(),  prep_in.id()  == p1a(0, id as int),
        prom_out.wf(), prom_out.id() == p1b(0, id as int),
        acc_in.wf(),   acc_in.id()   == p2a(0, id as int),
        accd_out.wf(), accd_out.id() == p2b(0, id as int),
        log.wf(),      log.id()      == alog(id as int),
        log.hist() == Seq::<PMsg>::empty(),
        prep_in.iid() == log.iid(), prom_out.iid() == log.iid(),
        acc_in.iid()  == log.iid(), accd_out.iid() == log.iid(),
    ensures a.inv(), a.np() == 1, a.id == id,
{
    let mut pi: Vec<In<PMsg, Paxos>> = Vec::new();  pi.push(prep_in);
    let mut po: Vec<Out<PMsg, Paxos>> = Vec::new(); po.push(prom_out);
    let mut ai: Vec<In<PMsg, Paxos>> = Vec::new();  ai.push(acc_in);
    let mut ao: Vec<Out<PMsg, Paxos>> = Vec::new(); ao.push(accd_out);
    let a = Acceptor {
        id,
        prepares:  FanIn  { ins:  pi, ids: Ghost(Seq::new(1nat, |p: int| p1a(p, id as int))) },
        promises:  FanOut { outs: po, ids: Ghost(Seq::new(1nat, |p: int| p1b(p, id as int))) },
        accepts:   FanIn  { ins:  ai, ids: Ghost(Seq::new(1nat, |p: int| p2a(p, id as int))) },
        accepteds: FanOut { outs: ao, ids: Ghost(Seq::new(1nat, |p: int| p2b(p, id as int))) },
        log,
        max_bal: Ballot { round: 0, prop: 0 },
        has_acc: false,
        acc_bal: Ballot { round: 0, prop: 0 },
        acc_val: 0,
    };
    assert(a.inv()) by {
        assert(a.prepares.ids@  =~= Seq::new(1nat, |p: int| p1a(p, id as int)));
        assert(a.promises.ids@  =~= Seq::new(1nat, |p: int| p1b(p, id as int)));
        assert(a.accepts.ids@   =~= Seq::new(1nat, |p: int| p2a(p, id as int)));
        assert(a.accepteds.ids@ =~= Seq::new(1nat, |p: int| p2b(p, id as int)));
    }
    a
}

} // verus!
