// COUNTEREXAMPLE. Expected to FAIL verification.
//
// The action writes to two channels but declares only one in its footprint.
// A second action with a "disjoint" footprint could then write the same
// undeclared channel, and the two would not commute. `lemma_frame` and
// `lemma_commutes` both reject it.

#[path = "../src/net.rs"] pub mod net;
#[path = "../src/api.rs"] pub mod api;

use vstd::prelude::*;
use net::*;
use api::*;

verus! {

pub enum Msg { Req(Ghost<ChanId>, Ghost<ChanId>) }

pub enum Act { A }

pub struct Bad;

impl Spec for Bad {

    type M = Msg;
    type A = Act;
    type S = Net<Msg>;


    open spec fn inv(net: Net<Msg>) -> bool { true }


    open spec fn gate(a: Act, req: Msg, n: Net<Msg>) -> bool { true }



    open spec fn step(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) -> bool {
        n1 == n0.do_send(req->Req_0@, resp).do_send(req->Req_1@, resp)
    }
}

impl Protocol for Bad {    type C = Fifo;

    proof fn lemma_recv_preserves(net: Net<Msg>, c: ChanId, m: Msg) { }

    // UNDERSTATED: `step` writes Req_0 AND Req_1; only Req_0 is declared.
    open spec fn footprint(a: Act, req: Msg) -> Set<ChanId> {
        Set::empty().insert(req->Req_0@)
    }


    proof fn lemma_frame(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) { }
    proof fn lemma_preserves_inv(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>) { }
    proof fn lemma_local_send(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) { }
    proof fn lemma_local_recv(a: Act, req: Msg, resp: Msg, n0: Net<Msg>, n1: Net<Msg>,
                              c: ChanId, m: Msg) { }
    proof fn lemma_commutes(a: Act, b: Act, ra: Msg, rb: Msg, sa: Msg, sb: Msg,
        n0: Net<Msg>, mid_ab: Net<Msg>, nab: Net<Msg>) { }
}

} // verus!

fn main() {}
