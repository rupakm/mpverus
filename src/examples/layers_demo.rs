// Layered refinement over a protocol's state machine.
//
// The bottom layer is not written here. It is `BottomLayer<(Beat, HbTok)>`, derived in
// `layer.rs` from the protocol's own state, invariant and transition relations,
// so what is refined is the protocol itself rather than a separate copy of it.
// This file supplies only the layer above and the mapping between them.
//
// The layer above is not a state machine state at all, but a pair holding a
// count and the last sequence number. That is the shape a specification
// normally has, and `abs_state` is the Abadi-Lamport refinement mapping.
//
// It also shows why `lemma_gate` and `lemma_step` may assume the concrete
// invariant. The abstraction keeps only the LAST sequence number, while the
// derived gate speaks of every element of the history; bridging the two
// requires knowing the history is increasing, which is exactly the invariant.
// Without that hypothesis this refinement is unprovable.

use vstd::prelude::*;
use crate::layer::*;
use crate::tok::*;
use crate::tok::ChanId;
use crate::examples::heartbeat::*;

verus!{

/// A coarser layer: how many beats have gone out, and the last one's number.
pub struct HbTop;
pub enum HbTopAct { Beat }

impl Spec for HbTop {
    type M = Beat;
    type A = HbTopAct;
    type S = (nat, u64);

    open spec fn inv(s: (nat, u64)) -> bool { true }

    /// The abstract gate can only speak of what the abstraction kept.
    open spec fn gate(a: HbTopAct, req: Beat, s: (nat, u64)) -> bool {
        s.0 > 0 ==> s.1 < req.seq
    }

    /// A beat is recorded -- or nothing happens. The second disjunct is how a
    /// state-DEPENDENT stutter is expressed: `abs_act` is a function of the
    /// action alone, so an action that is invisible only in some states must be
    /// absorbed here rather than mapped to `None`.
    open spec fn step(a: HbTopAct, req: Beat, resp: Beat,
                      s0: (nat, u64), s1: (nat, u64)) -> bool {
        (s1.0 == s0.0 + 1 && s1.1 == req.seq) || s1 == s0
    }
}

pub struct HbR;

impl Refines<BottomLayer<(Beat, HbTok)>, HbTop> for HbR {
    /// Forget everything but the beat count and the last sequence number.
    open spec fn abs_state(s: NetSM::State<Beat, HbTok>) -> (nat, u64) {
        let h = s.sent[link()];
        (h.len(), if h.len() > 0 { h.last().seq } else { 0 })
    }

    open spec fn abs_msg(m: Beat) -> Beat { m }

    /// A receive is ALWAYS invisible upstairs, so it maps to `None`. A send may
    /// or may not be, depending on the channel, which is why it maps to an
    /// action whose transition admits identity.
    open spec fn abs_act(a: ChanAct) -> Option<HbTopAct> {
        match a {
            ChanAct::Send(c) => Some(HbTopAct::Beat),
            ChanAct::Recv(c) => None,
        }
    }

    proof fn lemma_inv(s: NetSM::State<Beat, HbTok>) { }

    /// The abstraction kept only the LAST sequence number, but the derived gate
    /// speaks of every element. The invariant is what bridges them: the history
    /// is increasing, so the last element is the maximum.
    proof fn lemma_gate(a: ChanAct, req: Beat, s: NetSM::State<Beat, HbTok>) {
        if !s.sent.dom().contains(link()) { return; }
        let h = s.sent[link()];
        assert forall|x: int| 0 <= x < h.len() implies (#[trigger] h[x]).seq < req.seq by {
            if x < h.len() - 1 {
                assert(h[x].seq < h[h.len() - 1].seq);
            }
            assert(h.last() == h[h.len() - 1]);
        }
    }

    proof fn lemma_step(a: ChanAct, req: Beat, resp: Beat,
                        s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>) {
        match a {
            ChanAct::Recv(c) => {
                // A receive touches only `recvd`, which the mapping forgets.
                let qi = choose|q: Seq<Beat>, i: nat| <NetSM::State<Beat, HbTok>>::do_recv(s0, s1, c, q, i, req);
                assert(s1.sent =~= s0.sent);
                
            }
            ChanAct::Send(c) => {
                let q = choose|q: Seq<Beat>|
                    <NetSM::State<Beat, HbTok>>::do_send(s0, s1, c, q, req, Set::empty());
                
                if c == link() {
                    assert(s1.sent[link()] == q.push(req));
                    assert(s1.sent[link()].last() == req);
                } else {
                    assert(s1.sent[link()] == s0.sent[link()]);
                }
            }
        }
    }
}

/// Both directions of the refinement, exercised. Without these, `lift` and
/// `lift_stutter` have no callers and the layer API is unchecked in practice.
pub proof fn beat_is_visible(req: Beat, resp: Beat, s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>, c: ChanId)
    requires
        BottomLayer::<(Beat, HbTok)>::inv(s0),
        BottomLayer::<(Beat, HbTok)>::step(ChanAct::Send(c), req, resp, s0, s1),
        HbTop::gate(HbTopAct::Beat, HbR::abs_msg(req), HbR::abs_state(s0)),
    ensures
        HbTop::step(HbTopAct::Beat, HbR::abs_msg(req), HbR::abs_msg(resp),
                    HbR::abs_state(s0), HbR::abs_state(s1)),
{
    lift::<BottomLayer<(Beat, HbTok)>, HbTop, HbR>(ChanAct::Send(c), req, resp, s0, s1);
}

pub proof fn recv_is_invisible(req: Beat, resp: Beat, s0: NetSM::State<Beat, HbTok>, s1: NetSM::State<Beat, HbTok>, c: ChanId)
    requires
        BottomLayer::<(Beat, HbTok)>::inv(s0),
        BottomLayer::<(Beat, HbTok)>::step(ChanAct::Recv(c), req, resp, s0, s1),
    ensures
        // nothing happened upstairs
        HbR::abs_state(s1) == HbR::abs_state(s0),
{
    lift_stutter::<BottomLayer<(Beat, HbTok)>, HbTop, HbR>(ChanAct::Recv(c), req, resp, s0, s1);
}

}
