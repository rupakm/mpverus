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
}
}
