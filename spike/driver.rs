#![allow(unused_imports)]
// SPIKE, not integrated. Does `NetHandler` REPLACE `Process`, or sit under it?
//
// If a handler bundled with its mailbox is itself a `Process`, then `Process`
// stays as the driver-facing interface, `run` keeps working unchanged, and
// porting a protocol is opt-in rather than a migration.
#[path = "../src/tok.rs"]   pub mod tok;
#[path = "../src/proc.rs"]  pub mod proc;
#[path = "../src/layer.rs"] pub mod layer;
#[path = "../src/examples/leaselock.rs"] pub mod leaselock;

use vstd::prelude::*;
use vstd::tokens::InstanceId;
use crate::tok::*;
use crate::proc::*;
use crate::leaselock::*;

verus!{

/// A service that never blocks: `tick` is `N . L*` outbound, `handle` is
/// `N . L*` inbound. The blocking receive belongs to whoever drives it.
pub trait NetHandler<M, Inv: NetInv<M>> : Sized {
    spec fn wf(&self) -> bool;
    spec fn iid(&self) -> InstanceId;
    /// Which channel each mailbox slot is, as ONE value rather than a
    /// quantified relation. A `forall` here does not chain across the call to
    /// `tick`, because the fact recorded before the call is about a value that
    /// no longer has a name afterwards. A single equality does chain.
    spec fn chans(&self) -> Seq<ChanId>;

    /// Both halves must keep their identity: which machine they are on and
    /// which channel each mailbox slot is. Without this the driver cannot
    /// relate the witness it was handed to the slot it came from, because
    /// `chan` is a function of a service that just changed.
    fn tick(&mut self)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).chans() == old(self).chans();

    fn handle(&mut self, from: usize, m: M, Tracked(w): Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            w.instance_id() == old(self).iid(),
            w.element().0 == old(self).chans()[from as int],
            w.element().2 == m,
            Inv::wit_inv(old(self).chans()[from as int], m),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).chans() == old(self).chans();
}

/// A handler bundled with the mailbox it is driven from.
pub struct Driven<#[verifier::reject_recursive_types] M, Inv: NetInv<M>, H: NetHandler<M, Inv>> {
    pub h: H,
    pub inbox: Inbox<M, Inv>,
}

impl<M, Inv: NetInv<M>, H: NetHandler<M, Inv>> Driven<M, Inv, H> {
    /// The one place the two halves are related: mailbox slot `k` is the
    /// channel the handler says it is. A mismatch is caught here and nowhere
    /// else, which is the right place for it.
    pub open spec fn inv(&self) -> bool {
        &&& self.h.wf()
        &&& self.inbox.wf()
        &&& self.inbox.iid() == self.h.iid()
        &&& self.h.chans().len() == self.inbox.len()
        &&& forall|k: int| 0 <= k < self.inbox.rxs@.len()
                ==> (#[trigger] self.inbox.rxs@[k].id()) == self.h.chans()[k]
    }
}

/// THE POINT OF THE SPIKE. A handler and its mailbox ARE a `Process`, so
/// `Process` is not retired: it becomes the driver-facing interface, and
/// `NetHandler` becomes what a protocol author writes.
impl<M, Inv: NetInv<M>, H: NetHandler<M, Inv>> Process for Driven<M, Inv, H> {
    open spec fn wf(&self) -> bool { self.inv() }

    fn step(&mut self) {
        // Capture BOTH sides as ghost data before anything moves. The relation
        // between two immutable values persists across the calls; a quantified
        // fact about `self` does not, because `self` changes twice.
        let ghost ids0 = self.inbox.rxs@;
        let ghost cs0  = self.h.chans();
        assert(forall|j: int| 0 <= j < ids0.len() ==> (#[trigger] ids0[j].id()) == cs0[j]);

        self.h.tick();                                   // N . L*
        let (k, m, Tracked(w)) = self.inbox.recv_any_wit();  // the ONE interference point
        proof {
            // Slot k is still the channel the handler thinks it is: `tick`
            // preserved `chans`, and receiving preserved the mailbox's slots.
            assert(self.inbox.rxs@ =~= ids0);
            assert(self.h.chans() =~= cs0);
            assert(ids0[k as int].id() == cs0[k as int]);
        }
        self.h.handle(k, m, Tracked(w));                 // N . L*
    }
}

fn main() { }
}
