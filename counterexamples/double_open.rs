#![allow(unused_imports)]
// MUST FAIL TO COMPILE.
// EXPECT-ERROR: use of moved value
//
// Opening one channel twice. The second call is rejected by Rust's ownership
// rules rather than by the solver: `make_endpoints` consumes the channel's send
// and receive tokens, the machine holds exactly one of each, and the first call
// already took them.
//
// This is the strongest form the check can take. There is no proof obligation
// to discharge and no invariant to get right; the second call cannot be
// written down. Were it allowed, each call would create a fresh queue, so a
// sender from the first and a receiver from the second would be two unrelated
// queues that the model believes are one channel -- every proof still valid,
// and no message ever delivered.
#[path = "../src/tok.rs"]  pub mod tok;
#[path = "../src/proc.rs"] pub mod proc;

use vstd::prelude::*;
use crate::tok::*;

verus!{
pub struct Triv;

impl NetInv<u64> for Triv {
    open spec fn gate(c: ChanId, s: Seq<u64>, m: u64) -> bool { true }
    open spec fn wit_inv(c: ChanId, m: u64) -> bool { true }
    open spec fn deliverable_at(v: Seq<u64>, i: nat) -> bool { fifo_deliverable(v, i) }
    open spec fn extra(sent: Map<ChanId, Seq<u64>>) -> bool { true }
    open spec fn needs_cause(c: ChanId, m: u64) -> bool { false }
    open spec fn extra_gives2(c: ChanId, m1: u64, m2: u64) -> bool { true }
    proof fn lemma_extra_gives2(sent: Map<ChanId, Seq<u64>>, c: ChanId,
                                i: nat, j: nat, m1: u64, m2: u64) { }
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<u64>, m: u64) { }
    proof fn lemma_cause_gives(c: ChanId, m: u64, causes: Set<(ChanId, nat, u64)>) { }
    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_alloc(sent: Map<ChanId, Seq<u64>>, c: ChanId) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<u64>>,
                                   was_sent: Set<(ChanId, nat, u64)>,
                                   c: ChanId, s: Seq<u64>, m: u64,
                                   causes: Set<(ChanId, nat, u64)>) { }
}

pub fn open_it_twice(
    Tracked(stok): Tracked<NetSM::sent<u64, Triv>>,
    Tracked(rtok): Tracked<NetSM::recvd<u64, Triv>>,
)
    requires
        stok.key() == chan(0, seq![]),
        rtok.key() == chan(0, seq![]),
{
    let ghost c = chan(0, seq![]);
    let (_tx1, _rx1, Tracked(s2), Tracked(r2)) =
        make_endpoints::<u64, Triv>(Ghost(c), Tracked(stok), Tracked(rtok));

    // The tokens were moved into the call above. Passing the originals again is
    // a use-after-move; passing the returned ones would be a DIFFERENT channel
    // opening, which is exactly what must not be possible for one identifier.
    let (_tx2, _rx2, Tracked(_s3), Tracked(_r3)) =
        make_endpoints::<u64, Triv>(Ghost(c), Tracked(stok), Tracked(rtok));
}

fn main() { }
}
