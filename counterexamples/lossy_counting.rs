#![allow(unused_imports)]
// MUST FAIL TO VERIFY.
// EXPECT-ERROR: assertion failed|postcondition not satisfied|precondition not satisfied
//
// Under an unreliable link, two receives do NOT imply two distinct sends: the
// network is free to hand back the same packet twice. This file claims they do,
// and must be rejected.
//
// The FIFO counterpart of this claim IS provable -- see `two_are_distinct` in
// `src/heartbeat.rs`. The difference is entirely `deliverable_at`.
#[path = "../src/tok.rs"]   pub mod tok;
#[path = "../src/proc.rs"]  pub mod proc;
#[path = "../src/examples/lossy.rs"] pub mod lossy;

use vstd::prelude::*;
use vstd::tokens::{KeyValueToken, ElementToken};
use crate::tok::*;
use crate::lossy::*;

verus!{
pub fn count_two(
    rx: &Receiver<Pkt>,
    Tracked(inst): Tracked<&NetSM::Instance<Pkt, Lossy>>,
    Tracked(tok):  Tracked<&mut NetSM::recvd<Pkt, Lossy>>,
) -> (r: (Pkt, Pkt, Ghost<nat>, Ghost<nat>))
    requires
        rx.id() == link(),
        old(tok).instance_id() == inst.id(),
        old(tok).key() == rx.id(),
    ensures
        // BOGUS on an unreliable link.
        r.2@ != r.3@,
{
    let (a, wa) = recv::<Pkt, Lossy>(rx, Tracked(inst), Tracked(tok));
    let (b, wb) = recv::<Pkt, Lossy>(rx, Tracked(inst), Tracked(tok));
    (a, b, Ghost(wa@.element().1), Ghost(wb@.element().1))
}
}
fn main(){}
