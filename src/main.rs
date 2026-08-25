#![allow(unused_imports)]

// The library.
pub mod tok;
pub mod layer;
pub mod proc;
pub mod quorum;

// Protocols written against it.
pub mod examples;

use vstd::prelude::*;

verus!{
fn main() {
    demo();
}

/// A demonstration that the source Verus checks is the source that runs.
///
/// `deploy_lease` is ordinary verified code: it boots the machine, opens the
/// channels, builds the three lease-lock services and runs them on three
/// threads. Everything below the print goes through the endpoint API. Only the
/// printing is outside the proof, which is why this wrapper exists.
#[verifier::external_body]
pub fn demo() {
    let accepted = examples::lease_system::deploy_lease();
    println!("lease lock ran to completion; last write accepted = {}", accepted);

    // The same round, twice: all three acceptors up, then one never started.
    // A quorum is two, so the second must still commit.
    let v3 = examples::paxos_system::deploy_paxos(3, 1);
    println!("paxos, 3 of 3 acceptors up:      committed value = {}", v3);
    let v2 = examples::paxos_system::deploy_paxos(2, 1);
    println!("paxos, 2 of 3 acceptors up:      committed value = {}", v2);

    // Round two prefers 99, but a quorum has already accepted 42 and reports
    // it, so 42 is what the proposer is allowed to commit.
    let va = examples::paxos_system::deploy_paxos(3, 2);
    println!("paxos, second round wants 99:    committed value = {}", va);

    // Acceptors that know two proposers. Proposer 0 never starts, so the first
    // slot of every acceptor's mailbox stays silent for the whole run.
    let vt = examples::paxos_system::deploy_paxos_two(3);
    println!("paxos, 2 proposers, 0 silent:    committed value = {}", vt);
}
}
