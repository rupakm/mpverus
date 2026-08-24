#![allow(unused_imports)]
// SPIKE, not integrated. Can blocking be moved OUT of activities and into a
// driver, so that `R . N . L*` is a property of the type rather than of a
// comment, and `wf` becomes a genuine yield invariant?
//
// Today `Process::step` may block anywhere inside itself. `Writer::write_once`
// contains two blocking receives and nothing requires `wf` between them; it is
// sound only because every fact a service uses is owned or monotone, which
// nothing checks.
//
// The proposal: a service never receives. A driver owns the inbound endpoint,
// does the ONE blocking receive, and calls `handle`. Then the only interference
// point is between handler calls, at a place the type system knows about.
#[path = "../src/tok.rs"]  pub mod tok;
#[path = "../src/proc.rs"] pub mod proc;
#[path = "../src/examples/pingpong.rs"] pub mod pingpong;

use vstd::prelude::*;
use crate::tok::*;
use crate::proc::*;
use crate::pingpong::*;

verus!{

/// A service that reacts to messages and never blocks.
pub trait Handler : Sized {
    type Msg;

    spec fn wf(&self) -> bool;

    /// `N . L*`: local work and sends, no receive. The driver has already done
    /// the one blocking receive, so this cannot contain an interference point.
    fn handle(&mut self, m: Self::Msg)
        requires old(self).wf()
        ensures  final(self).wf();
}

/// The driver: the ONE place a blocking receive happens.
///
/// `wf` is required before the receive and re-established after the handler, so
/// it holds at the only point where another thread can interleave. That is what
/// makes it a yield invariant rather than a description of one.
pub fn serve<H: Handler<Msg = Msg>>(
    h: &mut H, inp: &mut In<Msg, PingPong>, rounds: usize,
)
    requires
        old(h).wf(), old(inp).wf(),
    ensures
        final(h).wf(), final(inp).wf(),
{
    let mut i: usize = 0;
    while i < rounds
        invariant h.wf(), inp.wf(),
        decreases rounds - i,
    {
        let m = inp.recv();          // the interference point, and the only one
        h.handle(m);
        i = i + 1;
    }
}

// ---------------------------------------------------------------------------
// The easy case: a responder is already `N . L*`.
// ---------------------------------------------------------------------------
pub struct Responder2 {
    pub rsp: Out<Msg, PingPong>,
    pub val: u64,
}

impl Handler for Responder2 {
    type Msg = Msg;

    open spec fn wf(&self) -> bool {
        self.rsp.wf() && self.rsp.id() == pong_chan() && ok(self.val)
    }

    fn handle(&mut self, m: Msg) {
        self.rsp.send(Msg::Pong(self.val));
    }
}

// ---------------------------------------------------------------------------
// The hard case: a service that INITIATES. A writer is not answering requests,
// it is driving a sequence -- so it needs somewhere to say what to do next when
// it is not reacting.
//
// Modelled as an explicit state, which is what "the writer is a state machine"
// actually means. `tick` is the outbound half; `handle` is the inbound half.
// Both are `N . L*`, so neither contains an interference point.
// ---------------------------------------------------------------------------
pub enum Phase { Idle, AwaitingReply }

pub trait Initiator : Handler {
    /// `N . L*`: decide what to send next. Called by the driver when this
    /// service is not waiting for anything.
    fn tick(&mut self)
        requires old(self).wf()
        ensures  final(self).wf();

    spec fn waiting(&self) -> bool;
}

pub struct Client2 {
    pub req:  Out<Msg, PingPong>,
    pub seen: u64,
    pub phase: Phase,
}

impl Handler for Client2 {
    type Msg = Msg;

    open spec fn wf(&self) -> bool {
        self.req.wf() && self.req.id() == ping_chan()
    }

    fn handle(&mut self, m: Msg) {
        match m {
            Msg::Pong(v) => { self.seen = v; self.phase = Phase::Idle; }
            _ => { }
        }
    }
}

impl Initiator for Client2 {
    open spec fn waiting(&self) -> bool { self.phase is AwaitingReply }

    fn tick(&mut self) {
        self.req.send(Msg::Ping);
        self.phase = Phase::AwaitingReply;
    }
}

/// A driver for a service that both initiates and reacts. Still exactly one
/// blocking receive per turn, and `wf` holds across it.
pub fn drive<H: Initiator<Msg = Msg>>(
    h: &mut H, inp: &mut In<Msg, PingPong>, rounds: usize,
)
    requires old(h).wf(), old(inp).wf(),
    ensures  final(h).wf(), final(inp).wf(),
{
    let mut i: usize = 0;
    while i < rounds
        invariant h.wf(), inp.wf(),
        decreases rounds - i,
    {
        h.tick();
        let m = inp.recv();          // the one interference point
        h.handle(m);
        i = i + 1;
    }
}

fn main() { }
}
