#![allow(unused_imports)]
// MUST FAIL TO VERIFY.
// EXPECT-ERROR: precondition not satisfied
//
// A writer that sends a write carrying a lease token it was never granted.
//
// Nothing on the write channel itself rules this out: the gate on `wr_req(w)`
// sees only that channel's history, and a forged token looks exactly like a
// real one. What rejects it is provenance. `needs_cause` marks writes as
// requiring justification, so they must go through `send_caused`, and
// `caused_by` pins the justification to a grant carrying that very token on
// this writer's own reply channel. The witness this writer holds is for the
// grant it actually received, which names a different token, so the
// precondition of `send_caused` cannot be discharged.
//
// The same mechanism rejects the two neighbouring cheats. Presenting another
// writer's grant fails because `caused_by` derives the expected channel from
// `c`, and going through plain `send` fails because `send` requires
// `!needs_cause`.
#[path = "../src/tok.rs"]                 pub mod tok;
#[path = "../src/proc.rs"]                pub mod proc;
#[path = "../src/abs.rs"]                 pub mod abs;
#[path = "../src/layer.rs"]               pub mod layer;
#[path = "../src/examples/leaselock.rs"]  pub mod leaselock;

use vstd::prelude::*;
use crate::tok::*;
use crate::proc::*;
use crate::leaselock::*;

verus!{
/// The honest `Writer::write_once`, with one line changed.
pub fn forging_write(
    id: usize,
    acq: &mut Out<Msg, Lease>,
    grt: &mut In<Msg, Lease>,
    wr:  &mut Out<Msg, Lease>,
    val: u64,
)
    requires
        old(acq).wf(), old(grt).wf(), old(wr).wf(),
        old(acq).id() == acq_req(id as int),
        old(grt).id() == acq_rsp(id as int),
        old(wr).id()  == wr_req(id as int),
        old(grt).iid() == old(wr).iid(),
{
    acq.send(Msg::Acquire);

    // The writer holds a witness for the grant it was actually given ...
    let (grant, Tracked(gw)) = grt.recv_wit();
    let token = match grant {
        Msg::Granted(t) => t,
        _ => { proof { assert(false); } 0 }
    };

    proof { assert(seq![id as int][0] == id as int); }

    // ... and then writes under a token of its own choosing.
    wr.send_caused(Msg::Write(999, 0, val), Tracked(&gw));
}

fn main() { }
}
