#![allow(unused_imports)]
// SPIKE, not integrated. THE DECIDING CASE for the `Handler` shape.
//
// `Writer::write_once` in `leaselock.rs` contains TWO blocking receives, on two
// different channels, with `wf` required at neither point between them. If the
// writer cannot be expressed as a non-blocking handler, the shape is wrong.
#[path = "../src/tok.rs"]  pub mod tok;
#[path = "../src/proc.rs"] pub mod proc;
#[path = "../src/layer.rs"] pub mod layer;
#[path = "../src/examples/leaselock.rs"] pub mod leaselock;

use vstd::prelude::*;
use vstd::tokens::{InstanceId, MapToken};
use crate::tok::*;
use crate::proc::*;
use crate::leaselock::*;

verus!{

/// A service that never blocks. The driver owns the mailbox and does the one
/// blocking receive; both methods here are `N . L*`.
///
/// `handle` takes the witness as well as the message, because a network service
/// may need it as provenance for something it sends later. That is what makes
/// this trait specific to network services rather than generic.
pub trait NetHandler<M, Inv: NetInv<M>> : Sized {
    spec fn wf(&self) -> bool;

    /// Which machine this service belongs to, and which channel the driver's
    /// mailbox slot `k` is. The driver must pass these facts in: a handler
    /// cannot branch on them, because they are ghost, and it must not re-derive
    /// them, because it does not own the mailbox.
    ///
    /// This is the part the spike found. Without it the writer's `handle` would
    /// have to test at run time that the witness it was handed came from the
    /// grant channel, which is not executable and would be the wrong shape
    /// anyway -- the fact is static.
    spec fn iid(&self) -> InstanceId;
    spec fn chan(&self, k: int) -> ChanId;

    /// Outbound half: decide what to send. Does nothing while waiting.
    fn tick(&mut self)
        requires old(self).wf() ensures final(self).wf();

    /// Inbound half.
    fn handle(&mut self, from: usize, m: M, Tracked(w): Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            w.instance_id() == old(self).iid(),
            w.element().0 == old(self).chan(from as int),
            w.element().2 == m,
            Inv::wit_inv(old(self).chan(from as int), m),
        ensures final(self).wf();
}

/// Which phase of its own protocol the writer is in. This is what "the writer
/// is a state machine" means concretely: the state that used to live between
/// two blocking receives inside one activity is now a field.
pub enum WPhase { Idle, AwaitingGrant, Holding, AwaitingAck }

pub struct Writer2 {
    pub id:  usize,
    pub acq: Out<Msg, Lease>,
    pub wr:  Out<Msg, Lease>,
    pub token: u64,
    pub seq: u64,
    pub val: u64,
    pub last_ok: bool,
    pub phase: WPhase,
    pub lease: Tracked<Option<NetSM::was_sent<Msg, Lease>>>,
}

impl NetHandler<Msg, Lease> for Writer2 {
    open spec fn iid(&self) -> InstanceId { self.wr.iid() }

    /// Slot 0 is the grant channel, slot 1 the acknowledgement channel.
    open spec fn chan(&self, k: int) -> ChanId {
        if k == 0 { acq_rsp(self.id as int) } else { wr_rsp(self.id as int) }
    }

    open spec fn wf(&self) -> bool {
        &&& self.acq.wf() && self.wr.wf()
        &&& self.acq.id() == acq_req(self.id as int)
        &&& self.wr.id()  == wr_req(self.id as int)
        &&& self.acq.iid() == self.wr.iid()
        &&& self.token != 0 ==> {
                &&& self.lease@ is Some
                &&& self.lease@->Some_0.instance_id() == self.wr.iid()
                &&& self.lease@->Some_0.element().0 == acq_rsp(self.id as int)
                &&& self.lease@->Some_0.element().2 == Msg::Granted(self.token)
            }
    }

    fn tick(&mut self) {
        match self.phase {
            WPhase::Idle => {
                self.acq.send(Msg::Acquire);
                self.phase = WPhase::AwaitingGrant;
            }
            WPhase::Holding => {
                if self.token != 0 && self.seq < u64::MAX {
                    let tracked gw;
                    proof { gw = (self.lease.borrow()).tracked_borrow(); }
                    let t = self.token;
                    let q = self.seq;
                    proof {
                        assert(seq![self.id as int][0] == self.id as int);
                        assert(self.wr.id().ix[0] == self.id as int);
                        let j0 = gw.element().1;
                        assert(set![gw.element()].contains(
                            (acq_rsp(self.id as int), j0, Msg::Granted(t))));
                        assert(Lease::caused_by(self.wr.id(), Msg::Write(t, q, self.val),
                                                set![gw.element()]));
                    }
                    self.wr.send_caused(Msg::Write(t, q, self.val), Tracked(gw));
                    self.phase = WPhase::AwaitingAck;
                }
            }
            _ => { }
        }
    }

    fn handle(&mut self, from: usize, m: Msg, Tracked(w): Tracked<NetSM::was_sent<Msg, Lease>>) {
        if from == 0 {
            // The grant channel.
            match m {
                Msg::Granted(t) => {
                    // No run-time check: `wit_inv` on the grant channel already
                    // says the token is nonzero, and the driver's precondition
                    // says this witness came from that channel.
                    self.token = t;
                    self.seq = 0;
                    proof { self.lease = Tracked(Some(w)); }
                    self.phase = WPhase::Holding;
                }
                _ => { self.phase = WPhase::Idle; }
            }
        } else {
            // The acknowledgement channel.
            match m {
                Msg::Accepted(_, _, _) => {
                    self.last_ok = true;
                    if self.seq < u64::MAX { self.seq = self.seq + 1; }
                    self.phase = WPhase::Holding;
                }
                _ => { self.last_ok = false; self.phase = WPhase::Holding; }
            }
        }
    }
}

fn main() { }
}
