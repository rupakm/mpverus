#![allow(unused_imports)]
// MUST FAIL TO COMPILE.
// EXPECT-ERROR: opaque datatype|field `id` of struct .* is private
//
// Relabelling a channel handle: taking the queue that belongs to one channel
// and rebuilding a handle that names another.
//
// This is the attack that motivates `Sender` and `Receiver` being opaque. If it
// were allowed, a send through the relabelled handle would satisfy every
// precondition -- the token's key would match the handle's declared name -- and
// would record one channel's history growing while the bytes went into a
// different queue. The receiver on that queue would then be handed a message
// that `recv`'s postcondition asserts was sent on its own channel, and was not.
// The trusted primitive's specification would be false at runtime, which is the
// one boundary the whole development rests on.
//
// Nothing about it is caught by the solver. It is refused because the type is
// opaque and its fields are private: only `make_endpoints` can produce a handle.
#[path = "../src/tok.rs"] pub mod tok;

use vstd::prelude::*;
use crate::tok::*;

verus!{
pub fn relabel<M>(a: Sender<M>, b: Ghost<ChanId>) -> (r: Sender<M>)
    ensures r.id() == b@,
{
    let Sender { id: _old, inner } = a;
    Sender { id: b, inner }
}

fn main() { }
}
