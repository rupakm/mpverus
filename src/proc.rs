// The programming model: services that own their endpoints.
//
// `tok.rs` gives channel primitives that take the state machine instance and a
// channel token as arguments. Writing a protocol directly against them means
// every function threads ghost state it does not otherwise care about, which is
// not how service code is organised.
//
// This module packages a channel endpoint together with the token for it, so a
// send is a method on the endpoint and carries no ghost arguments at all. A
// service is a struct holding its endpoints and its local state; its activities
// are ordinary methods; and `Process` is what a driver loop needs.
//
// Nothing here is trusted. Every operation is a verified wrapper over the
// primitives in `tok.rs`, and the endpoint invariants are proved, not assumed.

use vstd::prelude::*;
use vstd::tokens::{InstanceId, MapToken};
use crate::tok::*;

verus!{

// ---------------------------------------------------------------------------
// Endpoints that own their tokens.
// ---------------------------------------------------------------------------

/// An outbound endpoint: the sender handle, the token for that channel's send
/// history, and a handle to the machine. Holding the token here is what lets
/// `send` be a method rather than a call with four ghost arguments.
///
/// This is not duplicable, for the same reason `Sender` is not: a channel's
/// send history belongs to one sender, and that is what makes `send` a left
/// mover.
pub struct Out<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub tx:   Sender<M>,
    pub tok:  Tracked<NetSM::sent<M, Inv>>,
    pub inst: Tracked<NetSM::Instance<M, Inv>>,
}

impl<M, Inv: NetInv<M>> Out<M, Inv> {
    /// The channel this endpoint names.
    pub open spec fn id(&self) -> ChanId { self.tx.id() }
    /// Everything sent on it so far. Readable because this thread owns it.
    pub open spec fn hist(&self) -> Seq<M> { self.tok@.value() }
    /// Which machine it belongs to.
    pub open spec fn iid(&self) -> InstanceId { self.inst@.id() }

    /// The endpoint describes the channel it names, on the machine it names.
    /// Every method preserves this, so a service states it once.
    pub open spec fn wf(&self) -> bool {
        &&& self.tok@.instance_id() == self.inst@.id()
        &&& self.tok@.key() == self.tx.id()
    }

    /// Send. Non-blocking, and a left mover.
    pub fn send(&mut self, m: M) -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            Inv::gate(old(self).id(), old(self).hist(), m),
            !Inv::needs_cause(old(self).id(), m),
        ensures
            final(self).wf(),
            final(self).id()   == old(self).id(),
            final(self).iid()  == old(self).iid(),
            final(self).hist() == old(self).hist().push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(), old(self).hist().len(), m),
    {
        send::<M, Inv>(&self.tx, m, Tracked(self.inst.borrow()),
                       Tracked(self.tok.borrow_mut()))
    }

    /// Send a message that must point at one already sent elsewhere, presenting
    /// the witness for it. See the provenance section of the write-up.
    pub fn send_caused(&mut self, m: M, Tracked(cause): Tracked<&NetSM::was_sent<M, Inv>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            Inv::gate(old(self).id(), old(self).hist(), m),
            cause.instance_id() == old(self).iid(),
            Inv::caused_by(old(self).id(), m, set![cause.element()]),
        ensures
            final(self).wf(),
            final(self).id()   == old(self).id(),
            final(self).iid()  == old(self).iid(),
            final(self).hist() == old(self).hist().push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(), old(self).hist().len(), m),
    {
        send_caused::<M, Inv>(&self.tx, m, Tracked(self.inst.borrow()),
                              Tracked(self.tok.borrow_mut()), Tracked(cause))
    }
}

/// A remote call over well-defined channels: send a request on `self`, and
/// take the reply on a channel opened for the purpose.
///
/// Civl's synchronised asynchronous call. Both halves are left movers -- the
/// send because it is a send, the receive because the handler's reply has
/// already been accounted for -- so the whole call contains NO interference
/// point and is atomic to its caller. That is what makes an implementation
/// written as a sequence of calls readable as a sequential program.
///
/// `reply_cap` is the reply channel's send token, which the caller holds
/// because it opened that channel. Handing it over here is the handler's send,
/// executed at the call site.
impl<M, Inv: DetDelivery<M>> Out<M, Inv> {
    pub fn call(
        &mut self, req: M,
        reply: &mut In<M, Inv>,
        Tracked(reply_cap): Tracked<NetSM::sent<M, Inv>>,
        Ghost(expected): Ghost<M>,
    ) -> (m: M)
        requires
            old(self).wf(),
            Inv::gate(old(self).id(), old(self).hist(), req),
            !Inv::needs_cause(old(self).id(), req),
            old(reply).wf(),
            old(reply).iid() == old(self).iid(),
            reply_cap.instance_id() == old(self).iid(),
            reply_cap.key() == old(reply).id(),
            Inv::gate(old(reply).id(), reply_cap.value(), expected),
            !Inv::needs_cause(old(reply).id(), expected),
            Inv::deliverable_at(old(reply).rhist(), reply_cap.value().len()),
        ensures
            m == expected,
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).iid() == old(self).iid(),
            final(self).hist() == old(self).hist().push(req),
            final(reply).wf(),
            final(reply).id() == old(reply).id(),
            final(reply).iid() == old(reply).iid(),
    {
        rpc::<M, Inv>(
            &self.tx, req,
            &reply.rx, Ghost(expected),
            Tracked(self.inst.borrow()),
            Tracked(self.tok.borrow_mut()),
            Tracked(reply_cap),
            Tracked(reply.tok.borrow_mut()))
    }
}

/// An inbound endpoint. Not duplicable, which is where the single-consumer
/// discipline comes from.
pub struct In<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub rx:   Receiver<M>,
    pub tok:  Tracked<NetSM::recvd<M, Inv>>,
    pub inst: Tracked<NetSM::Instance<M, Inv>>,
}

impl<M, Inv: NetInv<M>> In<M, Inv> {
    pub open spec fn id(&self)  -> ChanId     { self.rx.id() }
    pub open spec fn iid(&self) -> InstanceId { self.inst@.id() }
    /// What this endpoint has consumed. Owned, so readable.
    pub open spec fn rhist(&self) -> Seq<M> { self.tok@.value() }

    pub open spec fn wf(&self) -> bool {
        &&& self.tok@.instance_id() == self.inst@.id()
        &&& self.tok@.key() == self.rx.id()
    }

    /// Receive, and learn the protocol's guarantee about what arrived. Blocking,
    /// a right mover, and an interference point: other services run while this
    /// one waits, so whatever is concluded here must survive their steps. The
    /// guarantee does, because it is about a message that was sent, and that
    /// record only grows.
    pub fn recv(&mut self) -> (m: M)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id()  == old(self).id(),
            final(self).iid() == old(self).iid(),
            Inv::wit_inv(final(self).id(), m),
            final(self).rhist() == old(self).rhist().push(m),
    {
        recv_learn::<M, Inv>(&self.rx, Tracked(self.inst.borrow()),
                             Tracked(self.tok.borrow_mut()))
    }

    /// Receive, keeping the witness. Needed when the message will later serve as
    /// provenance for one this service sends.
    pub fn recv_wit(&mut self) -> (r: (M, Tracked<NetSM::was_sent<M, Inv>>))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id()  == old(self).id(),
            final(self).iid() == old(self).iid(),
            r.1@.instance_id() == final(self).iid(),
            r.1@.element().0 == final(self).id(),
            r.1@.element().2 == r.0,
            Inv::wit_inv(final(self).id(), r.0),
            // Which position was delivered, which is what distinguishes two
            // receives on a link whose delivery is deterministic.
            Inv::deliverable_at(old(self).rhist(), r.1@.element().1),
            final(self).rhist() == old(self).rhist().push(r.0),
    {
        let (m, Tracked(w)) = recv::<M, Inv>(&self.rx, Tracked(self.inst.borrow()),
                                             Tracked(self.tok.borrow_mut()));
        proof { self.inst.borrow().learn(self.rx.id(), w.element().1, m, &w); }
        (m, Tracked(w))
    }
}

/// Several inbound channels a service waits on together.
///
/// A service with one `In` per peer must decide which to block on, so a silent
/// peer stops it serving anyone else. An `Inbox` waits on all of them and
/// reports which one produced a message, which is what a server accepting
/// connections from many clients actually needs.
///
/// The consumption records live in one `MapToken` rather than one token per
/// channel, because that is what the underlying primitive consumes.
pub struct Inbox<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub rxs:  Vec<Receiver<M>>,
    pub toks: Tracked<MapToken<ChanId, Seq<M>, NetSM::recvd<M, Inv>>>,
    pub inst: Tracked<NetSM::Instance<M, Inv>>,
}

impl<M, Inv: NetInv<M>> Inbox<M, Inv> {
    pub open spec fn id(&self, k: int) -> ChanId { self.rxs[k].id() }
    pub open spec fn len(&self) -> nat { self.rxs.len() as nat }
    pub open spec fn iid(&self) -> InstanceId { self.inst@.id() }

    pub open spec fn wf(&self) -> bool {
        &&& self.rxs.len() > 0
        &&& self.toks@.instance_id() == self.inst@.id()
        &&& forall|k: int| 0 <= k < self.rxs.len()
                ==> self.toks@.dom().contains(#[trigger] self.rxs[k].id())
    }

    /// Block until any peer sends, keeping the witness. Needed when the message
    /// may later serve as provenance for something this service sends.
    pub fn recv_any_wit(&mut self) -> (res: (usize, M, Tracked<NetSM::was_sent<M, Inv>>))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).rxs@ == old(self).rxs@,
            0 <= res.0 < final(self).rxs.len(),
            res.2@.instance_id() == final(self).iid(),
            res.2@.element().0 == final(self).id(res.0 as int),
            res.2@.element().2 == res.1,
            Inv::wit_inv(final(self).id(res.0 as int), res.1),
    {
        let (k, m, Tracked(w)) = recv_any::<M, Inv>(
            &self.rxs, Tracked(self.inst.borrow()), Tracked(self.toks.borrow_mut()));
        proof {
            self.inst.borrow().learn(self.rxs@[k as int].id(), w.element().1, m, &w);
        }
        (k, m, Tracked(w))
    }

    /// Block until any peer sends, and report which. The interference point.
    pub fn recv_any(&mut self) -> (res: (usize, M))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).rxs@ == old(self).rxs@,
            0 <= res.0 < final(self).rxs.len(),
            Inv::wit_inv(final(self).id(res.0 as int), res.1),
    {
        let (k, m, Tracked(w)) = recv_any::<M, Inv>(
            &self.rxs, Tracked(self.inst.borrow()), Tracked(self.toks.borrow_mut()));
        proof {
            self.inst.borrow().learn(self.rxs@[k as int].id(), w.element().1, m, &w);
        }
        (k, m)
    }
}

// ---------------------------------------------------------------------------
// Opening a channel.
// ---------------------------------------------------------------------------

/// Give a channel its two endpoints.
///
/// This CONSUMES the send and receive tokens for the channel, which is what
/// makes it callable at most once per channel: the machine holds exactly one of
/// each, and this takes both. A second attempt has nothing left to pass.
///
/// That matters for more than tidiness. The underlying primitive creates a
/// fresh queue each time it is called, so two calls for one channel identifier
/// would produce two unrelated queues that the model believes are one channel:
/// a sender writing into the first while a receiver waits on the second. The
/// proof would still hold and the program would never deliver anything. Taking
/// ownership of the tokens makes that unrepresentable, and pairs the two ends
/// with each other by construction.
///
/// A transport whose two ends live in different processes cannot do this, since
/// there is no token to pass between them; there the namespace belongs to the
/// operating system and binding to an already-bound address has to fail at run
/// time. For channels within one program, ownership is the stronger discipline
/// and costs no assumption.
///
/// Verified, not trusted.
pub fn open_channel<M, Inv: NetInv<M>>(
    c: Ghost<ChanId>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(stok): Tracked<NetSM::sent<M, Inv>>,
    Tracked(rtok): Tracked<NetSM::recvd<M, Inv>>,
) -> (res: (Out<M, Inv>, In<M, Inv>))
    requires
        stok.instance_id() == inst.id(), stok.key() == c@,
        rtok.instance_id() == inst.id(), rtok.key() == c@,
    ensures
        res.0.wf(), res.0.id() == c@, res.0.iid() == inst.id(),
        res.0.hist() == stok.value(),
        res.1.wf(), res.1.id() == c@, res.1.iid() == inst.id(),
{
    let (tx, rx, Tracked(s2), Tracked(r2)) =
        make_endpoints::<M, Inv>(c, Tracked(stok), Tracked(rtok));
    let tracked i1 = inst.clone();
    let tracked i2 = inst.clone();
    (Out { tx, tok: Tracked(s2), inst: Tracked(i1) },
     In  { rx, tok: Tracked(r2), inst: Tracked(i2) })
}

/// Create a channel while the program runs, and give it its endpoints.
///
/// Freshness comes from the machine's allocator: `mint` proves the name is one
/// no channel has used, so the tokens it returns are genuinely new and this
/// cannot collide with an existing channel.
///
/// Verified, not trusted.
pub fn open_new_channel<M, Inv: NetInv<M>>(
    fam: Ghost<nat>, j: usize,
    Tracked(inst):  Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(alloc): Tracked<&mut NetSM::next<M, Inv>>,
) -> (res: (Out<M, Inv>, In<M, Inv>))
    requires
        old(alloc).instance_id() == inst.id(),
    ensures
        final(alloc).instance_id() == inst.id(),
        final(alloc).value() == old(alloc).value() + 1,
        res.0.wf(), res.1.wf(),
        res.0.id() == dyn_chan(fam@, j as int, old(alloc).value()),
        res.1.id() == res.0.id(),
        res.0.iid() == inst.id(), res.1.iid() == inst.id(),
        // Both halves start empty, which is what a first call on this channel
        // needs in order to be deliverable.
        res.0.hist() == Seq::<M>::empty(),
        res.1.rhist() == Seq::<M>::empty(),
{
    let (tx, rx, Tracked(stok), Tracked(rtok)) =
        mint::<M, Inv>(fam, j, Tracked(inst), Tracked(alloc));
    let tracked i1 = inst.clone();
    let tracked i2 = inst.clone();
    (Out { tx, tok: Tracked(stok), inst: Tracked(i1) },
     In  { rx, tok: Tracked(rtok), inst: Tracked(i2) })
}

// ---------------------------------------------------------------------------
// Services.
// ---------------------------------------------------------------------------

/// A participant in a protocol.
///
/// `wf` is the service's invariant. It is the yield invariant of every
/// interference point inside its activities, and what a deployment must
/// establish before the service is first run. Because each activity is
/// separately required to preserve it, each is independently a block that
/// reduction may treat as atomic.
pub trait Process : Sized {
    spec fn wf(&self) -> bool;

    /// One turn of the service loop. A service with several activities
    /// dispatches to them from here; they are ordinary methods with the same
    /// `wf`-to-`wf` contract.
    fn step(&mut self)
        requires old(self).wf()
        ensures  final(self).wf();
}

/// A service that NEVER BLOCKS, so that `R . N . L*` is a property of the type
/// rather than of a comment.
///
/// `Process::step` may block anywhere inside itself, which is why `wf` is only
/// an invariant at activity entry and exit: a body with two blocking receives
/// has an interference point in the middle where nothing is required. A
/// `NetHandler` cannot block at all. The driver owns the mailbox, performs the
/// one blocking receive, and calls the handler around it, so `wf` is required
/// and re-established at the only point where another thread can interleave.
///
/// Both halves are needed. `handle` is the reactive half; `tick` is for a
/// service that INITIATES, which cannot be expressed as answering a request.
/// A service that only reacts leaves `tick` empty.
pub trait NetHandler<M, Inv: NetInv<M>> : Sized {
    spec fn wf(&self) -> bool;

    /// Which machine this service is on.
    spec fn iid(&self) -> InstanceId;

    /// Which channel each mailbox slot is, as ONE value rather than a
    /// quantified relation. The driver must pass this in: a handler cannot
    /// branch on it, because it is ghost, and must not re-derive it, because it
    /// does not own the mailbox. A `Seq` rather than a function of an index
    /// because a `forall` does not chain across the call to `tick`.
    spec fn chans(&self) -> Seq<ChanId>;

    /// The outbound half: decide what to send. `N . L*`.
    fn tick(&mut self)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).chans() == old(self).chans();

    /// The inbound half. `N . L*`. The witness comes with the message, because
    /// a service may need it as provenance for something it sends later.
    fn handle(&mut self, from: usize, m: M, Tracked(w): Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            // Without this the channel lookup is unspecified and the guarantee
            // below says nothing.
            0 <= from < old(self).chans().len(),
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
///
/// This is why `NetHandler` does not replace `Process`: a `Driven` IS a
/// `Process`, so `run` and every deployment are unchanged, and adopting the
/// handler shape is per-service rather than a migration.
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
        &&& self.h.chans().len() == self.inbox.rxs@.len()
        &&& forall|k: int| 0 <= k < self.inbox.rxs@.len()
                ==> (#[trigger] self.inbox.rxs@[k].id()) == self.h.chans()[k]
    }
}

impl<M, Inv: NetInv<M>, H: NetHandler<M, Inv>> Process for Driven<M, Inv, H> {
    open spec fn wf(&self) -> bool { self.inv() }

    /// One turn: `N . L*`, then the single blocking receive, then `N . L*`.
    /// Repeating this is `(R . N . L*)*` -- a sequence of atomic blocks with a
    /// checked invariant between them, which is what `run` does.
    fn step(&mut self) {
        // Capture both sides as ghost DATA before anything moves. A relation
        // between two immutable values survives the calls; a quantified fact
        // about `self` does not, because `self` changes twice.
        let ghost ids0 = self.inbox.rxs@;
        let ghost cs0  = self.h.chans();
        assert(forall|j: int| 0 <= j < ids0.len() ==> (#[trigger] ids0[j].id()) == cs0[j]);

        self.h.tick();
        let (k, m, Tracked(w)) = self.inbox.recv_any_wit();
        proof {
            assert(self.inbox.rxs@ =~= ids0);
            assert(self.h.chans() =~= cs0);
            assert(ids0[k as int].id() == cs0[k as int]);
        }
        self.h.handle(k, m, Tracked(w));
    }
}

/// Drive a service. Protocol-independent: the invariant a service preserves is
/// exactly the invariant this loop needs.
pub fn run<P: Process>(p: &mut P, rounds: usize)
    requires old(p).wf(),
    ensures  final(p).wf(),
{
    let mut i: usize = 0;
    while i < rounds
        invariant p.wf(),
        decreases rounds - i,
    {
        p.step();
        i = i + 1;
    }
}

} // verus!
