// ONE PROCESS, SEVERAL THREADS.
//
// A thread here is a unit of sequential control that OWNS a service. Sibling
// threads of one process are, as far as the proof is concerned, ordinary
// unrelated threads, and forking is handing each one its service.
//
// Nothing has to be assumed to divide ownership. A service holds its endpoints
// and their tokens as ordinary `Tracked` fields, so it moves into a spawned
// closure like any other value, and two services cannot name the same channel
// because there is only one token for it.
use vstd::prelude::*;
use crate::tok::*;
use crate::proc::*;
use crate::examples::twophase_fanout::*;

verus! {

/// Fork one thread per participant, then join and take the services back.
///
/// Compare the earlier version of this file, which carved tokens out of two
/// maps by hand and reassembled them on the way out. A service is already the
/// unit of ownership, so there is nothing left to divide.
pub fn run_participants(p0: Participant, p1: Participant)
    requires
        p0.wf(), p1.wf(),
{
    let h0 = vstd::thread::spawn(move || -> (r: Participant)
        ensures r.wf()
        { let mut p = p0; p.step(); p });

    let h1 = vstd::thread::spawn(move || -> (r: Participant)
        ensures r.wf()
        { let mut p = p1; p.step(); p });

    match (h0.join(), h1.join()) {
        // Each child hands its service back, invariant intact.
        (Ok(_a), Ok(_b)) => { }
        // A panicked child took its service with it, tokens and all.
        _ => { abort_on_panicked_child() }
    }
}

} // verus!
