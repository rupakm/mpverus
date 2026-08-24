#![allow(unused_imports)]
// MUST FAIL TO VERIFY.
// EXPECT-ERROR: assertion failed|precondition not satisfied
//
// The gate on `TpcfSM::do_send` says only participant j's OWN vote may appear
// on participant j's reply channel. This participant votes yes regardless of
// what it was actually given, and must be rejected.
//
// This is the token-model successor to the old `nonlocal_gate` and
// `understated_footprint` counterexamples, which are now in `attic/`. Those
// tested obligations that no longer exist: footprints are gone, because a
// thread can only touch channels whose tokens it holds, and a gate cannot read
// another channel's state because it is not given one. What remains checkable
// is the gate itself, and this is it.
#[path = "../src/tok.rs"]             pub mod tok;
#[path = "../src/proc.rs"]            pub mod proc;
#[path = "../src/examples/twophase_fanout.rs"] pub mod twophase_fanout;

use vstd::prelude::*;
use vstd::tokens::KeyValueToken;
use crate::tok::*;
use crate::proc::*;
use crate::twophase_fanout::*;

verus!{
/// The honest `Participant::step`, with one word changed.
pub fn dishonest(p: &mut Participant)
    requires old(p).wf(),
{
    proof { config(); }
    let _m = p.req.recv();
    // BOGUS: not necessarily this participant's vote.
    p.rsp.send(FMsg::Vote(true));
}
}
fn main(){}
