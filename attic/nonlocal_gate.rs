// COUNTEREXAMPLE. Expected to FAIL verification.
//
// The action is gated on a channel OUTSIDE its footprint being empty, so an
// unrelated append disables it. `send` is then not a left mover with respect to
// this action, and skipping the yield after a send would be unsound.
// `lemma_local_send` and `lemma_local_recv` reject it.

#[path = "../src/net.rs"] pub mod net;
#[path = "../src/api.rs"] pub mod api;

use vstd::prelude::*;
use net::*;
use api::*;

verus! {

pub enum Msg { Req(Ghost<ChanId>, Ghost<ChanId>) }

pub enum Act { A }

pub struct Gated;

impl Spec for Gated {

    type M = Msg;
    type A = Act;
    type S = Net<Msg>;


    open spec fn inv(net: Net<Msg>) -> bool { true }


    open spec fn gate(a: Act, req: Msg, n: Net<Msg>) -> bool { true }

    // READS Req_1, which is not in the footprint.
    open spec fn step(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) -> bool {
        n0.sent(req->Req_1@).len() == 0 && n1 == n0.do_send(req->Req_0@, resp)
    }
}

impl Protocol for Gated {    type C = Fifo;

    proof fn lemma_recv_preserves(net: Net<Msg>, c: ChanId, m: Msg) { }

    open spec fn footprint(a: Act, req: Msg) -> Set<ChanId> {
        Set::empty().insert(req->Req_0@)
    }




    proof fn lemma_frame(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) {
        assert forall|c: ChanId| !Self::footprint(a, req).contains(c)
            implies #[trigger] n1.chans[c] == n0.chans[c] by { assert(c != req->Req_0@); }
    }
    proof fn lemma_preserves_inv(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) { }
    proof fn lemma_local_send(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) { }
    proof fn lemma_local_recv(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) { }
    proof fn lemma_commutes(a: Act, b: Act, ra: Msg, rb: Msg, sa: Msg, sb: Msg,
        n0: Net<Msg>, mid_ab: Net<Msg>, nab: Net<Msg>) {
        lemma_sends_commute(n0, ra->Req_0@, sa, rb->Req_0@, sb);
    }
}

} // verus!

fn main() {}
