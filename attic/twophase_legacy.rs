// Two-phase commit: the coordinator is written as ORDINARY SEQUENTIAL RUST,
// with the distributed prepare phase expressed as a loop of RPC calls.
// The safety proof is a plain sequential loop invariant.

use vstd::prelude::*;
use crate::net::*;
use crate::api::*;
use crate::layer::*;

verus! {

pub enum Msg {
    /// Carries the identity of this call's private reply channel -- the model's
    /// stand-in for moving a linear reply `Sender` into the request.
    Prepare(Ghost<ChanId>),
    Vote(bool),
    Decide(bool),
}

/// The complete 2PC protocol: message type, channel model, yield invariant,
/// and action pool, in one declaration.
pub struct Tpc;

/// `Local` is an internal step: the participant computing its vote, say. It
/// touches no channel. It exists to be INVISIBLE from the layer above --- see
/// `TpcRefines` at the bottom of this file.
pub enum TpcAct { Prepare, Local }

impl Spec for Tpc {

    type M = Msg;
    type A = TpcAct;
    type S = Net<Msg>;


    open spec fn inv(net: Net<Msg>) -> bool { true }


    open spec fn gate(a: TpcAct, req: Msg, n: Net<Msg>) -> bool { true }



    open spec fn step(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) -> bool {
        match a {
            TpcAct::Prepare => resp is Vote && n1 == n0.do_send(req->Prepare_0@, resp),
            TpcAct::Local   => n1 == n0,
        }
    }
}

impl Protocol for Tpc {    type C = Fifo;


    proof fn lemma_recv_preserves(net: Net<Msg>, c: ChanId, m: Msg) { }

    open spec fn footprint(a: TpcAct, req: Msg) -> Set<ChanId> {
        match a {
            TpcAct::Prepare => Set::empty().insert(req->Prepare_0@),
            TpcAct::Local   => Set::empty(),
        }
    }


    proof fn lemma_frame(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) {
        assert forall|c: ChanId| !Self::footprint(a, req).contains(c)
            implies #[trigger] n1.chans[c] == n0.chans[c] by {
            if a is Prepare { assert(c != req->Prepare_0@); }
        }
        assert(n0.dom().subset_of(n1.dom()));
    }

    proof fn lemma_preserves_inv(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) { }

    proof fn lemma_local_send(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) {
        if a is Prepare {
            assert(Self::footprint(a, req).contains(req->Prepare_0@));
            lemma_sends_commute(n0, req->Prepare_0@, resp, c, m);
        }
    }

    proof fn lemma_local_recv(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) {
        if a is Prepare {
            assert(Self::footprint(a, req).contains(req->Prepare_0@));
            lemma_send_recv_commute(n0, req->Prepare_0@, resp, c, m);
        }
    }

    /// Two prepare handlers with disjoint footprints reply on different
    /// channels, so their appends commute.
    proof fn lemma_commutes(
        a: TpcAct, b: TpcAct, ra: Msg, rb: Msg, sa: Msg, sb: Msg,
        n0: Net<Msg>, mid_ab: Net<Msg>, nab: Net<Msg>,
    ) {
        // A `Local` step changes nothing, so it commutes with anything.
        match (a, b) {
            (TpcAct::Local, _) => {
                assert(Self::step(b, rb, sb, n0, nab) && Self::step(a, ra, sa, nab, nab));
            }
            (_, TpcAct::Local) => {
                assert(Self::step(b, rb, sb, n0, n0) && Self::step(a, ra, sa, n0, nab));
            }
            (TpcAct::Prepare, TpcAct::Prepare) => {
                assert(Self::footprint(a, ra).contains(ra->Prepare_0@));
                assert(ra->Prepare_0@ != rb->Prepare_0@);
                lemma_sends_commute(n0, ra->Prepare_0@, sa, rb->Prepare_0@, sb);
                let mid = n0.do_send(rb->Prepare_0@, sb);
                assert(Self::step(b, rb, sb, n0, mid) && Self::step(a, ra, sa, mid, nab));
            }
        }
    }
}

/// The participant's prepare handler, as a member of that pool.
pub struct PrepareH;

impl Handler<Tpc> for PrepareH {
    open spec fn me() -> TpcAct { TpcAct::Prepare }

    open spec fn reply_chan(req: Msg) -> ChanId { req->Prepare_0@ }

    proof fn lemma_reply_in_footprint(req: Msg) { }

    proof fn lemma_nonblocking(req: Msg, n0: Net<Msg>) {
        let resp = Msg::Vote(true);
        let n1 = n0.do_send(Self::reply_chan(req), resp);
        assert(Tpc::step(Self::me(), req, resp, n0, n1));
    }

    proof fn lemma_reply_effect(req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) { }
}

/// The vote recorded on participant `j`'s response channel, if any.
pub open spec fn voted_yes(net: Net<Msg>, rsp: ChanId) -> bool {
    net.sent(rsp).len() > 0 && net.sent(rsp)[0] == Msg::Vote(true)
}

pub open spec fn replied(net: Net<Msg>, rsp: ChanId) -> bool {
    net.sent(rsp).len() > 0
}

/// The coordinator. Each iteration MINTS its own reply channel with `oneshot`,
/// so the freshness that makes the remote call atomic is produced here rather
/// than assumed as a precondition. The returned ghost sequence records which
/// channel each participant answered on.
pub fn coordinator(
    reqs: &Vec<Sender<Msg>>,
    Tracked(t): Tracked<&mut NetToken<Tpc>>,
) -> (res: (bool, Ghost<Seq<ChanId>>))
    requires
        forall|j: int| 0 <= j < reqs.len() ==> #[trigger] old(t).net.dom().contains(reqs[j].id@),
    ensures
        res.1@.len() == reqs.len(),
        // SAFETY: commit only if every participant voted yes.
        res.0 ==> forall|j: int| 0 <= j < reqs.len()
            ==> voted_yes(final(t).net, #[trigger] res.1@[j]),
{
    let mut i: usize = 0;
    let mut all_yes: bool = true;
    let ghost mut ids: Seq<ChanId> = Seq::empty();

    while i < reqs.len()
        invariant
            0 <= i <= reqs.len(),
            ids.len() == i,
            forall|j: int| 0 <= j < reqs.len() ==> #[trigger] t.net.dom().contains(reqs[j].id@),
            forall|j: int| 0 <= j < i ==> #[trigger] t.net.dom().contains(ids[j]),
            // every minted channel is distinct from every request channel ...
            forall|j: int, k: int| 0 <= j < i && 0 <= k < reqs.len()
                ==> #[trigger] ids[j] != #[trigger] reqs[k].id@,
            // ... and from every other minted channel
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i && j != k
                ==> #[trigger] ids[j] != #[trigger] ids[k],
            all_yes ==> forall|j: int| 0 <= j < i ==> voted_yes(t.net, #[trigger] ids[j]),
        decreases reqs.len() - i,
    {
        let ghost n0 = t.net;

        // Mint this call's private reply channel. In a system with real
        // handles, `_reply_tx` is what gets moved into the request message.
        let (_reply_tx, reply_rx) = oneshot::<Tpc>(Tracked(t));
        let ghost rid = reply_rx.id@;
        let ghost n1 = t.net;
        proof {
            assert(!n0.dom().contains(rid));
            assert forall|j: int| 0 <= j < i implies #[trigger] ids[j] != rid by {
                assert(n0.dom().contains(ids[j]));
            }
        }

        let req = Msg::Prepare(Ghost(reply_rx.id@));
        let ghost qid = reqs[i as int].id@;
        proof { lemma_do_send_dom(n1, qid, req); }

        let resp = rpc::<Tpc, PrepareH>(&reqs[i], req, &reply_rx, Tracked(t));

        proof {
            let n2 = n1.do_send(qid, req);
            lemma_do_send_dom(n2, rid, resp);
            lemma_do_recv_dom(n2.do_send(rid, resp), rid, resp);
            assert(t.net == n2.do_send(rid, resp).do_recv(rid, resp));
            assert(t.net.sent(rid) =~= Seq::<Msg>::empty().push(resp));
            // framing: neither the request send nor the reply touched an
            // earlier reply channel
            assert forall|j: int| 0 <= j < i
                implies #[trigger] t.net.sent(ids[j]) == n0.sent(ids[j]) by {
                assert(ids[j] != rid);
                assert(ids[j] != qid);
            }
            ids = ids.push(rid);
        }

        match resp {
            Msg::Vote(b) => { if !b { all_yes = false; } }
            _ => { all_yes = false; }
        }
        i = i + 1;
    }
    (all_yes, Ghost(ids))
}

/// The other side: a participant handler. This is the `R* . N . L*` shape --
/// blocking receive (right mover), local compute, sends (left mover) -- so it
/// needs exactly ONE yield point per iteration, at the receive, rather than one
/// per channel operation. `vote` is the participant's local decision.
pub fn participant(
    rx: &Receiver<Msg>,
    tx: &Sender<Msg>,
    vote: bool,
    rounds: usize,
    Tracked(t): Tracked<&mut NetToken<Tpc>>,
)
    requires
        old(t).net.dom().contains(rx.id@),
        old(t).net.dom().contains(tx.id@),
        old(t).recv_owned.contains(rx.id@),
        Tpc::inv(old(t).net),
{
    let mut k: usize = 0;
    while k < rounds
        invariant
            t.net.dom().contains(rx.id@),
            t.net.dom().contains(tx.id@),
            t.recv_owned.contains(rx.id@),
            Tpc::inv(t.net),
        decreases rounds - k,
    {
        // YIELD POINT (the only one in the block): blocking receive. Both
        // phases of the protocol arrive on the same channel, so one receive
        // serves both, and the participant needs one interference point per
        // iteration rather than one per protocol phase.
        let msg = recv::<Tpc>(rx, Tracked(t));
        proof { lemma_do_recv_dom(t.net, rx.id@, msg); }
        match msg {
            // Phase 1: vote. Left mover, so no yield after it -- the send and
            // the receive that preceded it are one atomic block.
            Msg::Prepare(_) => {
                send::<Tpc>(tx, Msg::Vote(vote), Tracked(t));
                proof { lemma_do_send_dom(t.net, tx.id@, Msg::Vote(vote)); }
            }
            // Phase 2: learn the outcome. Purely local: the participant
            // commits or aborts and sends nothing.
            Msg::Decide(_b) => { }
            Msg::Vote(_) => { }
        }
        k = k + 1;
    }
}

// ---------------------------------------------------------------------------
// LAYER 2. An abstraction whose STATE IS NOT A NETWORK.
//
// Two-phase commit, seen from above, is not a collection of channels: it is a
// record of who has voted yes. That is the shape a TLA or Leslie model of the
// protocol has, and `abs_state` is the Abadi--Lamport refinement mapping that
// recovers it from the message history.
//
// This layer also exercises stuttering. `TpcAct::Local` -- a participant
// computing its vote -- is invisible here, so it maps to `None`.
// ---------------------------------------------------------------------------

/// The abstract state: the set of reply channels that carry a yes vote.
pub struct Tally { pub yes: ISet<ChanId> }

pub struct TpcAbs;

pub enum TpcAbsAct { Record }

impl Spec for TpcAbs {
    type M = Msg;
    type A = TpcAbsAct;
    type S = Tally;

    open spec fn inv(s: Tally) -> bool { true }

    open spec fn gate(a: TpcAbsAct, req: Msg, s: Tally) -> bool { true }

    /// A vote is recorded, or it is not; the abstraction does not say which
    /// channel carried it or in what order. It says only that the tally grows
    /// by at most the one channel this action replied on.
    open spec fn step(a: TpcAbsAct, req: Msg, resp: Msg, s0: Tally, s1: Tally) -> bool {
        &&& s0.yes.subset_of(s1.yes)
        &&& forall|c: ChanId| s1.yes.contains(c) && !s0.yes.contains(c)
                ==> c == req->Prepare_0@
    }
}

/// The refinement mapping, and the proof that the implementation follows it.
pub struct TpcRefines;

impl Refines<Tpc, TpcAbs> for TpcRefines {
    /// A channel is in the tally exactly when a yes vote is first on it. This
    /// is a genuine change of state space: `Net<Msg>` down here, `Tally` up
    /// there.
    open spec fn abs_state(n: Net<Msg>) -> Tally {
        Tally { yes: ISet::new(|c: ChanId| n.dom().contains(c) && voted_yes(n, c)) }
    }

    open spec fn abs_msg(m: Msg) -> Msg { m }

    /// The internal step is INVISIBLE from above.
    open spec fn abs_act(a: TpcAct) -> Option<TpcAbsAct> {
        match a {
            TpcAct::Prepare => Some(TpcAbsAct::Record),
            TpcAct::Local   => None,
        }
    }

    proof fn lemma_inv(n: Net<Msg>) { }

    proof fn lemma_gate(a: TpcAct, req: Msg, n: Net<Msg>) { }

    proof fn lemma_step(a: TpcAct, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) {
        match a {
            TpcAct::Local => {
                // `n1 == n0`, so the mapping cannot have moved.
                assert(Self::abs_state(n1) == Self::abs_state(n0));
            }
            TpcAct::Prepare => {
                let rc = req->Prepare_0@;
                let s0 = Self::abs_state(n0);
                let s1 = Self::abs_state(n1);
                // Only the reply channel changed, so only it can enter the tally.
                assert forall|c: ChanId| s0.yes.contains(c) implies s1.yes.contains(c) by {
                    if c != rc {
                        // Only `rc` was touched, and inserting `rc` cannot
                        // remove `c` from the domain.
                        assert(n1.sent(c) == n0.sent(c));
                        assert(n1.dom().contains(c) == n0.dom().contains(c));
                    }
                }
                assert(s0.yes.subset_of(s1.yes));
                assert forall|c: ChanId| s1.yes.contains(c) && !s0.yes.contains(c)
                    implies c == rc by {
                    if c != rc { assert(n1.sent(c) == n0.sent(c)); }
                }
            }
        }
    }
}

/// Both directions of the refinement, exercised. A `Prepare` is raised to the
/// abstract `Record`; a `Local` step is absorbed into stuttering and is not an
/// abstract step at all.
pub proof fn tpc_layer_demo(req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>)
    requires
        Tpc::step(TpcAct::Prepare, req, resp, n0, n1),
    ensures
        TpcAbs::step(TpcAbsAct::Record, req, resp,
                     TpcRefines::abs_state(n0), TpcRefines::abs_state(n1)),
{
    lift::<Tpc, TpcAbs, TpcRefines>(TpcAct::Prepare, req, resp, n0, n1);
}

pub proof fn tpc_stutter_demo(req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>)
    requires
        Tpc::step(TpcAct::Local, req, resp, n0, n1),
    ensures
        // Nothing happened upstairs.
        TpcRefines::abs_state(n1) == TpcRefines::abs_state(n0),
{
    lift_stutter::<Tpc, TpcAbs, TpcRefines>(TpcAct::Local, req, resp, n0, n1);
}

} // verus!
