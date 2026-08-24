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
use vstd::tokens::{InstanceId, MapToken, SetToken};
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
            Inv::caused_by1(old(self).id(), m,
                            cause.element().0, cause.element().1, cause.element().2),
        ensures
            final(self).wf(),
            final(self).id()   == old(self).id(),
            final(self).iid()  == old(self).iid(),
            final(self).hist() == old(self).hist().push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(), old(self).hist().len(), m),
    {
        proof {
            // The bridge from the per-cause form to the set form the primitive
            // wants. Written once, here, instead of at every call site.
            Inv::lemma_caused_by1(self.tx.id(), m,
                                  cause.element().0, cause.element().1, cause.element().2);
            assert(set![(cause.element().0, cause.element().1, cause.element().2)]
                   =~= set![cause.element()]);
        }
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

impl<M, Inv: NetInv<M>> Out<M, Inv> {
    /// Send a message justified by exactly two earlier ones.
    pub fn send_caused2(&mut self, m: M,
                        Tracked(c1): Tracked<&NetSM::was_sent<M, Inv>>,
                        Tracked(c2): Tracked<&NetSM::was_sent<M, Inv>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            Inv::gate(old(self).id(), old(self).hist(), m),
            c1.instance_id() == old(self).iid(),
            c2.instance_id() == old(self).iid(),
            Inv::caused_by2(old(self).id(), m,
                            c1.element().0, c1.element().1, c1.element().2,
                            c2.element().0, c2.element().1, c2.element().2),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).iid() == old(self).iid(),
            final(self).hist() == old(self).hist().push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(), old(self).hist().len(), m),
    {
        let tracked cs;
        proof {
            Inv::lemma_caused_by2(self.tx.id(), m,
                                  c1.element().0, c1.element().1, c1.element().2,
                                  c2.element().0, c2.element().1, c2.element().2);
            let tracked mut acc = SetToken::empty(self.inst@.id());
            acc.insert(*c1);
            acc.insert(*c2);
            cs = acc;
            assert(cs.set() =~= set![
                (c1.element().0, c1.element().1, c1.element().2),
                (c2.element().0, c2.element().1, c2.element().2)]);
        }
        send_general::<M, Inv>(&self.tx, m, Tracked(self.inst.borrow()),
                               Tracked(self.tok.borrow_mut()), Tracked(&cs))
    }

    /// Send a message justified by SEVERAL earlier ones -- a quorum, say.
    pub fn send_general(&mut self, m: M,
                        Tracked(causes): Tracked<&SetToken<(ChanId, nat, M), NetSM::was_sent<M, Inv>>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            Inv::gate(old(self).id(), old(self).hist(), m),
            causes.instance_id() == old(self).iid(),
            Inv::needs_cause(old(self).id(), m)
                ==> Inv::caused_by(old(self).id(), m, causes.set()),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).iid() == old(self).iid(),
            final(self).hist() == old(self).hist().push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(), old(self).hist().len(), m),
    {
        send_general::<M, Inv>(&self.tx, m, Tracked(self.inst.borrow()),
                               Tracked(self.tok.borrow_mut()), Tracked(causes))
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

// ---------------------------------------------------------------------------
// Vectors of endpoints.
//
// A service with one peer per slot holds a vector of endpoints, and its
// invariant is a quantifier over that vector. Written out by hand this leaks a
// Verus fact into every such protocol: a quantified fact about `self` does not
// survive a call that changes `self`, so each mutation needs the quantifier
// taken apart and rebuilt, and each call into an element needs it instantiated
// first. That is mechanical, identical every time, and scales with the number
// of services rather than the number of ideas.
//
// `FanOut` and `FanIn` own the vector and the quantifier together. The
// `assert forall` is written once, here.
//
// The channel names live alongside as GHOST DATA that these types promise never
// to change. That is what makes the arrangement work: the protocol's own
// invariant is about `ids@` -- an immutable value -- rather than about the
// endpoints, so it survives every operation without being re-established.
// ---------------------------------------------------------------------------

/// One outbound endpoint per slot.
pub struct FanOut<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub outs: Vec<Out<M, Inv>>,
    /// Which channel each slot is. Fixed when the fan is built.
    pub ids: Ghost<Seq<ChanId>>,
}

impl<M, Inv: NetInv<M>> FanOut<M, Inv> {
    pub open spec fn len(&self) -> nat { self.outs.len() as nat }
    pub open spec fn id(&self, k: int) -> ChanId { self.ids@[k] }
    pub open spec fn hist(&self, k: int) -> Seq<M> { self.outs@[k].hist() }
    pub open spec fn iid(&self) -> InstanceId { self.outs@[0].iid() }

    /// Everything except being non-empty, so a fan can be built slot by slot.
    pub open spec fn pre_wf(&self) -> bool {
        &&& self.ids@.len() == self.outs.len()
        &&& forall|k: int| 0 <= k < self.outs@.len() ==> {
                &&& (#[trigger] self.outs@[k]).wf()
                &&& self.outs@[k].id() == self.ids@[k]
                &&& self.outs@[k].iid() == self.outs@[0].iid()
            }
    }

    pub open spec fn wf(&self) -> bool { self.outs.len() > 0 && self.pre_wf() }

    pub fn new() -> (f: Self)
        ensures f.pre_wf(), f.len() == 0, f.ids@ == Seq::<ChanId>::empty(),
    { FanOut { outs: Vec::new(), ids: Ghost(Seq::empty()) } }

    /// Add one outbound endpoint, in slot order. The slot's channel name is
    /// taken from the endpoint, so a fan cannot be built with the wrong names.
    pub fn add(&mut self, e: Out<M, Inv>)
        requires
            old(self).pre_wf(), e.wf(),
            old(self).len() > 0 ==> e.iid() == old(self).iid(),
        ensures
            final(self).pre_wf(),
            final(self).len() == old(self).len() + 1,
            final(self).ids@ =~= old(self).ids@.push(e.id()),
            old(self).len() > 0 ==> final(self).iid() == old(self).iid(),
            old(self).len() == 0 ==> final(self).iid() == e.iid(),
            forall|k: int| 0 <= k < old(self).len()
                ==> #[trigger] final(self).hist(k) == old(self).hist(k),
            final(self).hist(old(self).len() as int) == e.hist(),
    {
        let ghost c = e.id();
        let ghost n0 = self.outs@.len();
        self.outs.push(e);
        proof { self.ids = Ghost(self.ids@.push(c)); }
        assert forall|k: int| 0 <= k < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[k]).wf()
            &&& self.outs@[k].id() == self.ids@[k]
            &&& self.outs@[k].iid() == self.outs@[0].iid()
        } by {
            if k < n0 { assert(self.outs@[k] == old(self).outs@[k]); }
        }
    }

    /// How many slots, at run time.
    pub fn count(&self) -> (n: usize)
        requires self.wf(),
        ensures  n == self.len(),
    { self.outs.len() }

    /// Send on slot `k`, justified by one earlier message.
    pub fn send_caused(&mut self, k: usize, m: M,
                       Tracked(cause): Tracked<&NetSM::was_sent<M, Inv>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            k < old(self).len(),
            Inv::gate(old(self).id(k as int), old(self).hist(k as int), m),
            cause.instance_id() == old(self).iid(),
            Inv::caused_by1(old(self).id(k as int), m,
                            cause.element().0, cause.element().1, cause.element().2),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            final(self).hist(k as int) == old(self).hist(k as int).push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(k as int), old(self).hist(k as int).len(), m),
    {
        let ghost o0 = self.outs@;
        assert(self.outs@[k as int].wf());
        let w = self.outs[k].send_caused(m, Tracked(cause));
        assert forall|j: int| 0 <= j < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[j]).wf()
            &&& self.outs@[j].id() == self.ids@[j]
            &&& self.outs@[j].iid() == self.outs@[0].iid()
        } by {
            if j != k as int { assert(self.outs@[j] == o0[j]); }
            if k as int != 0 { assert(self.outs@[0] == o0[0]); }
        }
        w
    }

    /// Send on slot `k`, justified by exactly two earlier messages.
    pub fn send_caused2(&mut self, k: usize, m: M,
                        Tracked(c1): Tracked<&NetSM::was_sent<M, Inv>>,
                        Tracked(c2): Tracked<&NetSM::was_sent<M, Inv>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            k < old(self).len(),
            Inv::gate(old(self).id(k as int), old(self).hist(k as int), m),
            c1.instance_id() == old(self).iid(),
            c2.instance_id() == old(self).iid(),
            Inv::caused_by2(old(self).id(k as int), m,
                            c1.element().0, c1.element().1, c1.element().2,
                            c2.element().0, c2.element().1, c2.element().2),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            final(self).hist(k as int) == old(self).hist(k as int).push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(k as int), old(self).hist(k as int).len(), m),
    {
        let ghost o0 = self.outs@;
        assert(self.outs@[k as int].wf());
        let w = self.outs[k].send_caused2(m, Tracked(c1), Tracked(c2));
        assert forall|j: int| 0 <= j < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[j]).wf()
            &&& self.outs@[j].id() == self.ids@[j]
            &&& self.outs@[j].iid() == self.outs@[0].iid()
        } by {
            if j != k as int { assert(self.outs@[j] == o0[j]); }
            if k as int != 0 { assert(self.outs@[0] == o0[0]); }
        }
        w
    }

    /// Send on slot `k`, justified by several earlier messages.
    pub fn send_general(&mut self, k: usize, m: M,
                        Tracked(causes): Tracked<&SetToken<(ChanId, nat, M), NetSM::was_sent<M, Inv>>>)
        -> (w: Tracked<NetSM::was_sent<M, Inv>>)
        requires
            old(self).wf(),
            k < old(self).len(),
            Inv::gate(old(self).id(k as int), old(self).hist(k as int), m),
            causes.instance_id() == old(self).iid(),
            Inv::needs_cause(old(self).id(k as int), m)
                ==> Inv::caused_by(old(self).id(k as int), m, causes.set()),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            final(self).hist(k as int) == old(self).hist(k as int).push(m),
            w@.instance_id() == final(self).iid(),
            w@.element() == (final(self).id(k as int), old(self).hist(k as int).len(), m),
    {
        let ghost o0 = self.outs@;
        assert(self.outs@[k as int].wf());
        let w = self.outs[k].send_general(m, Tracked(causes));
        assert forall|j: int| 0 <= j < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[j]).wf()
            &&& self.outs@[j].id() == self.ids@[j]
            &&& self.outs@[j].iid() == self.outs@[0].iid()
        } by {
            if j != k as int { assert(self.outs@[j] == o0[j]); }
            if k as int != 0 { assert(self.outs@[0] == o0[0]); }
        }
        w
    }

    /// Send on slot `k`. The quantifier is re-established inside.
    pub fn send(&mut self, k: usize, m: M)
        requires
            old(self).wf(),
            k < old(self).len(),
            Inv::gate(old(self).id(k as int), old(self).hist(k as int), m),
            !Inv::needs_cause(old(self).id(k as int), m),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            final(self).hist(k as int) == old(self).hist(k as int).push(m),
            forall|j: int| 0 <= j < final(self).len() && j != k as int
                ==> #[trigger] final(self).hist(j) == old(self).hist(j),
    {
        let ghost o0 = self.outs@;
        assert(self.outs@[k as int].wf());
        self.outs[k].send(m);
        assert forall|j: int| 0 <= j < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[j]).wf()
            &&& self.outs@[j].id() == self.ids@[j]
            &&& self.outs@[j].iid() == self.outs@[0].iid()
        } by {
            if j != k as int { assert(self.outs@[j] == o0[j]); }
            if k as int != 0 { assert(self.outs@[0] == o0[0]); }
        }
        assert forall|j: int| 0 <= j < self.outs@.len() && j != k as int
            implies #[trigger] self.outs@[j].hist() == o0[j].hist() by {
            assert(self.outs@[j] == o0[j]);
        }
    }
}

/// A remote call on slot `k`. Proof-level, like `Out::call`, whose contract and
/// limitations this inherits.
impl<M, Inv: DetDelivery<M>> FanOut<M, Inv> {
    pub fn call(
        &mut self, k: usize, req: M,
        reply: &mut In<M, Inv>,
        Tracked(reply_cap): Tracked<NetSM::sent<M, Inv>>,
        Ghost(expected): Ghost<M>,
    ) -> (m: M)
        requires
            old(self).wf(),
            k < old(self).len(),
            Inv::gate(old(self).id(k as int), old(self).hist(k as int), req),
            !Inv::needs_cause(old(self).id(k as int), req),
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
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            final(reply).wf(),
            final(reply).id() == old(reply).id(),
            final(reply).iid() == old(reply).iid(),
    {
        let ghost o0 = self.outs@;
        assert(self.outs@[k as int].wf());
        let m = self.outs[k].call(req, reply, Tracked(reply_cap), Ghost(expected));
        assert forall|j: int| 0 <= j < self.outs@.len() implies {
            &&& (#[trigger] self.outs@[j]).wf()
            &&& self.outs@[j].id() == self.ids@[j]
            &&& self.outs@[j].iid() == self.outs@[0].iid()
        } by {
            if j != k as int { assert(self.outs@[j] == o0[j]); }
            if k as int != 0 { assert(self.outs@[0] == o0[0]); }
        }
        m
    }
}

/// One inbound endpoint per slot, for a service that blocks on a chosen peer.
/// A service that must wait on ALL of them wants `Inbox` instead.
pub struct FanIn<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub ins: Vec<In<M, Inv>>,
    pub ids: Ghost<Seq<ChanId>>,
}

impl<M, Inv: NetInv<M>> FanIn<M, Inv> {
    pub open spec fn len(&self) -> nat { self.ins.len() as nat }
    pub open spec fn id(&self, k: int) -> ChanId { self.ids@[k] }
    pub open spec fn iid(&self) -> InstanceId { self.ins@[0].iid() }

    /// Everything except being non-empty, so a fan can be built slot by slot.
    pub open spec fn pre_wf(&self) -> bool {
        &&& self.ids@.len() == self.ins.len()
        &&& forall|k: int| 0 <= k < self.ins@.len() ==> {
                &&& (#[trigger] self.ins@[k]).wf()
                &&& self.ins@[k].id() == self.ids@[k]
                &&& self.ins@[k].iid() == self.ins@[0].iid()
            }
    }

    pub open spec fn wf(&self) -> bool { self.ins.len() > 0 && self.pre_wf() }

    pub fn new() -> (f: Self)
        ensures f.pre_wf(), f.len() == 0, f.ids@ == Seq::<ChanId>::empty(),
    { FanIn { ins: Vec::new(), ids: Ghost(Seq::empty()) } }

    /// Add one inbound endpoint, in slot order.
    pub fn add(&mut self, e: In<M, Inv>)
        requires
            old(self).pre_wf(), e.wf(),
            old(self).len() > 0 ==> e.iid() == old(self).iid(),
        ensures
            final(self).pre_wf(),
            final(self).len() == old(self).len() + 1,
            final(self).ids@ =~= old(self).ids@.push(e.id()),
            old(self).len() > 0 ==> final(self).iid() == old(self).iid(),
            old(self).len() == 0 ==> final(self).iid() == e.iid(),
    {
        let ghost c = e.id();
        let ghost n0 = self.ins@.len();
        self.ins.push(e);
        proof { self.ids = Ghost(self.ids@.push(c)); }
        assert forall|k: int| 0 <= k < self.ins@.len() implies {
            &&& (#[trigger] self.ins@[k]).wf()
            &&& self.ins@[k].id() == self.ids@[k]
            &&& self.ins@[k].iid() == self.ins@[0].iid()
        } by {
            if k < n0 { assert(self.ins@[k] == old(self).ins@[k]); }
        }
    }

    pub fn count(&self) -> (n: usize)
        requires self.wf(),
        ensures  n == self.len(),
    { self.ins.len() }

    /// Receive on slot `k`, with the protocol's guarantee. Interference point.
    pub fn recv(&mut self, k: usize) -> (m: M)
        requires old(self).wf(), k < old(self).len(),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            Inv::wit_inv(old(self).id(k as int), m),
    {
        let ghost i0 = self.ins@;
        assert(self.ins@[k as int].wf());
        let m = self.ins[k].recv();
        assert forall|j: int| 0 <= j < self.ins@.len() implies {
            &&& (#[trigger] self.ins@[j]).wf()
            &&& self.ins@[j].id() == self.ids@[j]
            &&& self.ins@[j].iid() == self.ins@[0].iid()
        } by {
            if j != k as int { assert(self.ins@[j] == i0[j]); }
            if k as int != 0 { assert(self.ins@[0] == i0[0]); }
        }
        m
    }

    /// Receive on slot `k`, keeping the witness, for use as provenance.
    pub fn recv_wit(&mut self, k: usize) -> (r: (M, Tracked<NetSM::was_sent<M, Inv>>))
        requires old(self).wf(), k < old(self).len(),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            final(self).ids@ == old(self).ids@,
            final(self).iid() == old(self).iid(),
            Inv::wit_inv(old(self).id(k as int), r.0),
            r.1@.instance_id() == old(self).iid(),
            r.1@.element().0 == old(self).id(k as int),
            r.1@.element().2 == r.0,
    {
        let ghost i0 = self.ins@;
        assert(self.ins@[k as int].wf());
        let (m, Tracked(w)) = self.ins[k].recv_wit();
        assert forall|j: int| 0 <= j < self.ins@.len() implies {
            &&& (#[trigger] self.ins@[j]).wf()
            &&& self.ins@[j].id() == self.ids@[j]
            &&& self.ins@[j].iid() == self.ins@[0].iid()
        } by {
            if j != k as int { assert(self.ins@[j] == i0[j]); }
            if k as int != 0 { assert(self.ins@[0] == i0[0]); }
        }
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
/// Like `FanOut` and `FanIn`, the mailbox carries its channel names as
/// IMMUTABLE ghost data. That is what lets a service state which peer is on
/// which slot as a single equality between values rather than as a quantifier
/// over `rxs`, which every receive would otherwise invalidate.
pub struct Inbox<#[verifier::reject_recursive_types] M, Inv: NetInv<M>> {
    pub rxs:  Vec<Receiver<M>>,
    pub ids:  Ghost<Seq<ChanId>>,
    pub toks: Tracked<MapToken<ChanId, Seq<M>, NetSM::recvd<M, Inv>>>,
    pub inst: Tracked<NetSM::Instance<M, Inv>>,
}

impl<M, Inv: NetInv<M>> Inbox<M, Inv> {
    pub open spec fn id(&self, k: int) -> ChanId { self.ids@[k] }
    pub open spec fn len(&self) -> nat { self.rxs.len() as nat }
    pub open spec fn iid(&self) -> InstanceId { self.inst@.id() }

    /// Everything except being non-empty, so a mailbox can be built up slot by
    /// slot and only has to be complete before it is used.
    pub open spec fn pre_wf(&self) -> bool {
        &&& self.ids@.len() == self.rxs.len()
        &&& self.toks@.instance_id() == self.inst@.id()
        &&& forall|k: int| 0 <= k < self.rxs.len() ==> {
                &&& (#[trigger] self.rxs[k]).id() == self.ids@[k]
                &&& self.toks@.dom().contains(self.rxs[k].id())
            }
    }

    pub open spec fn wf(&self) -> bool { self.rxs.len() > 0 && self.pre_wf() }

    /// An empty mailbox.
    pub fn empty(Tracked(inst): Tracked<NetSM::Instance<M, Inv>>) -> (b: Self)
        ensures b.pre_wf(), b.iid() == inst.id(), b.len() == 0, b.ids@ == Seq::<ChanId>::empty(),
    {
        let tracked toks = MapToken::empty(inst.id());
        Inbox {
            rxs: Vec::new(), ids: Ghost(Seq::empty()),
            toks: Tracked(toks), inst: Tracked(inst),
        }
    }

    /// Add one inbound endpoint, in slot order.
    ///
    /// The endpoint is taken apart HERE, once, so no deployment has to reach
    /// into `rx` and `tok` itself -- which is the one place a caller could pair
    /// a receiver with a different channel's consumption record.
    pub fn add(&mut self, e: In<M, Inv>)
        requires old(self).pre_wf(), e.wf(), e.iid() == old(self).iid(),
        ensures
            final(self).pre_wf(),
            final(self).iid() == old(self).iid(),
            final(self).len() == old(self).len() + 1,
            final(self).ids@ =~= old(self).ids@.push(e.id()),
    {
        let ghost c = e.id();
        let ghost n0 = self.rxs@.len();
        let rx = e.rx;
        proof { self.toks.borrow_mut().insert(e.tok.get()); }
        self.rxs.push(rx);
        proof { self.ids = Ghost(self.ids@.push(c)); }
        assert forall|k: int| 0 <= k < self.rxs.len() implies {
            &&& (#[trigger] self.rxs[k]).id() == self.ids@[k]
            &&& self.toks@.dom().contains(self.rxs[k].id())
        } by {
            if k < n0 { assert(self.rxs@[k] == old(self).rxs@[k]); }
        }
    }

    /// Block until any peer sends, keeping the witness. Needed when the message
    /// may later serve as provenance for something this service sends.
    pub fn recv_any_wit(&mut self) -> (res: (usize, M, Tracked<NetSM::was_sent<M, Inv>>))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).rxs@ == old(self).rxs@,
            final(self).ids@ == old(self).ids@,
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

    /// How many peers this mailbox waits on.
    pub fn count(&self) -> (r: usize)
        ensures r == self.len(),
    { self.rxs.len() }

    /// Gather messages from `need` DISTINCT peers, first come first served.
    ///
    /// This is the shape a quorum-based service actually wants. Waiting on one
    /// peer at a time makes progress depend on every peer it names; waiting on
    /// all of them and stopping at `need` makes progress depend only on there
    /// being `need` live ones. A service built out of `recv` cannot be made to
    /// tolerate a crashed peer by any amount of proof, because the dependency
    /// is in the control flow.
    ///
    /// Messages that `accept` rejects, and repeats from a peer already counted,
    /// are dropped: their consumption records are consumed and their witnesses
    /// discarded. `accept` is the round filter -- a service running rounds must
    /// not count a reply to a round it has left.
    ///
    /// The witnesses for the messages that ARE counted are accumulated into one
    /// `SetToken`, which is what a quorum obligation is stated over. The caller
    /// gets three facts about it: every counted message has a witness in the
    /// set, the set holds NOTHING ELSE, and the sources are pairwise distinct.
    /// Together those turn a quorum argument into a counting argument on
    /// `srcs.len()`.
    ///
    /// `p` is the specification of `accept`. Verus cannot see inside an exec
    /// closure, so the caller states what the closure decides and proves the
    /// closure decides it; `collect` then reports `p` of everything it kept.
    ///
    /// This loop does not terminate if fewer than `need` peers ever send an
    /// accepted message. That is the protocol's liveness assumption and is not
    /// discharged here; safety does not depend on it. The attribute below is
    /// the only place in the development where a termination check is waived.
    ///
    /// Verified, not trusted.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn collect<F: Fn(usize, &M) -> bool>(
        &mut self,
        need: usize,
        p: Ghost<spec_fn(int, M) -> bool>,
        accept: F,
    ) -> (res: (Vec<usize>, Vec<M>, Tracked<SetToken<(ChanId, nat, M), NetSM::was_sent<M, Inv>>>,
                Ghost<Seq<nat>>))
        requires
            old(self).wf(),
            need <= old(self).rxs.len(),
            forall|k: usize, m: &M| #[trigger] call_requires(accept, (k, m)),
            forall|k: usize, m: &M, r: bool|
                #[trigger] call_ensures(accept, (k, m), r) ==> r == p@(k as int, *m),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).ids@ == old(self).ids@,
            res.0.len() == need,
            res.1.len() == need,
            res.2@.instance_id() == final(self).iid(),
            // Every source is a real peer, and no peer is counted twice.
            forall|i: int| 0 <= i < need ==> #[trigger] res.0@[i] < final(self).rxs.len(),
            forall|i: int, j: int|
                0 <= i < need && 0 <= j < need && i != j
                    ==> #[trigger] res.0@[i] != #[trigger] res.0@[j],
            // Everything counted passed the filter, and its witness is named:
            // `res.3` is the position each one occupies in its channel, so a
            // caller reads the record entry off rather than choosing it.
            res.3@.len() == need,
            forall|i: int| 0 <= i < need
                ==> #[trigger] p@(res.0@[i] as int, res.1@[i])
                    && Inv::wit_inv(final(self).id(res.0@[i] as int), res.1@[i])
                    && res.2@.set().contains(
                        (final(self).id(res.0@[i] as int), res.3@[i], res.1@[i])),
            // ... and the set holds nothing else.
            forall|e: (ChanId, nat, M)| res.2@.set().contains(e)
                ==> exists|i: int| 0 <= i < need
                        && e.0 == final(self).id(#[trigger] res.0@[i] as int)
                        && e.1 == res.3@[i] && e.2 == res.1@[i],
    {
        let mut srcs: Vec<usize> = Vec::new();
        let mut msgs: Vec<M> = Vec::new();
        let tracked mut cs = SetToken::empty(self.inst@.id());
        let ghost ids0 = self.ids@;
        let ghost mut poss: Seq<nat> = Seq::empty();

        // One flag per peer, so a chatty peer cannot fill the quorum alone.
        let n = self.rxs.len();
        let mut seen: Vec<bool> = vec![false; n];

        while srcs.len() < need
            invariant
                self.wf(),
                self.ids@ == ids0,
                self.inst@.id() == old(self).iid(),
                need <= ids0.len(),
                seen.len() == ids0.len(),
                srcs.len() == msgs.len(),
                poss.len() == srcs.len(),
                srcs.len() <= need,
                cs.instance_id() == old(self).iid(),
                forall|k: usize, m: &M| #[trigger] call_requires(accept, (k, m)),
                forall|k: usize, m: &M, r: bool|
                    #[trigger] call_ensures(accept, (k, m), r) ==> r == p@(k as int, *m),
                forall|i: int| 0 <= i < srcs.len() ==> #[trigger] srcs@[i] < ids0.len(),
                forall|i: int| 0 <= i < srcs.len() ==> seen@[#[trigger] srcs@[i] as int],
                forall|i: int, j: int|
                    0 <= i < srcs.len() && 0 <= j < srcs.len() && i != j
                        ==> #[trigger] srcs@[i] != #[trigger] srcs@[j],
                forall|i: int| 0 <= i < srcs.len()
                    ==> #[trigger] p@(srcs@[i] as int, msgs@[i])
                        && Inv::wit_inv(ids0[srcs@[i] as int], msgs@[i])
                        && cs.set().contains(
                            (ids0[srcs@[i] as int], poss[i], msgs@[i])),
                forall|e: (ChanId, nat, M)| cs.set().contains(e)
                    ==> exists|i: int| 0 <= i < srcs.len()
                            && e == (ids0[#[trigger] srcs@[i] as int], poss[i], msgs@[i]),
        {
            let (k, m, Tracked(w)) = self.recv_any_wit();
            if !seen[k] && accept(k, &m) {
                let ghost e = w.element();
                let ghost s0 = cs.set();
                let ghost srcs0 = srcs@;
                let ghost msgs0 = msgs@;
                let ghost poss0 = poss;
                proof { cs.insert(w); }
                seen.set(k, true);
                srcs.push(k);
                msgs.push(m);
                proof {
                    poss = poss.push(e.1);
                    assert(cs.set() =~= s0.insert(e));
                    assert(srcs@ =~= srcs0.push(k));
                    assert(msgs@ =~= msgs0.push(m));
                    assert(poss =~= poss0.push(e.1));
                    assert(e == (ids0[k as int], e.1, m));
                    assert forall|i: int| 0 <= i < srcs0.len() implies
                        #[trigger] p@(srcs@[i] as int, msgs@[i])
                        && Inv::wit_inv(ids0[srcs@[i] as int], msgs@[i])
                        && cs.set().contains((ids0[srcs@[i] as int], poss[i], msgs@[i])) by {
                        assert(srcs@[i] == srcs0[i]);
                        assert(msgs@[i] == msgs0[i]);
                        assert(poss[i] == poss0[i]);
                        assert(p@(srcs0[i] as int, msgs0[i]));
                    }
                    // Nothing else got in: the set grew by exactly one element,
                    // and that element is the one just pushed.
                    assert forall|x: (ChanId, nat, M)| cs.set().contains(x) implies
                        exists|i: int| 0 <= i < srcs@.len()
                            && x == (ids0[#[trigger] srcs@[i] as int], poss[i], msgs@[i]) by {
                        if x == e {
                            assert(srcs@[srcs0.len() as int] == k);
                            assert(msgs@[srcs0.len() as int] == m);
                            assert(poss[srcs0.len() as int] == e.1);
                        } else {
                            let i0 = choose|i: int| 0 <= i < srcs0.len()
                                && x == (ids0[srcs0[i] as int], poss0[i], msgs0[i]);
                            assert(srcs@[i0] == srcs0[i0]);
                            assert(msgs@[i0] == msgs0[i0]);
                            assert(poss[i0] == poss0[i0]);
                        }
                    }
                    // Distinctness: `k` was unmarked, every earlier source is marked.
                    assert forall|i: int, j: int|
                        0 <= i < srcs@.len() && 0 <= j < srcs@.len() && i != j
                            implies #[trigger] srcs@[i] != #[trigger] srcs@[j] by {
                        if i < srcs0.len() && j < srcs0.len() {
                            assert(srcs@[i] == srcs0[i] && srcs@[j] == srcs0[j]);
                        }
                    }
                }
            }
        }
        proof {
            assert(srcs.len() == need);
            assert forall|i: int| 0 <= i < need implies
                #[trigger] p@(srcs@[i] as int, msgs@[i])
                && Inv::wit_inv(self.id(srcs@[i] as int), msgs@[i])
                && cs.set().contains((self.id(srcs@[i] as int), poss[i], msgs@[i])) by {
                assert(p@(srcs@[i] as int, msgs@[i]));
                assert(self.id(srcs@[i] as int) == ids0[srcs@[i] as int]);
            }
            assert forall|x: (ChanId, nat, M)| cs.set().contains(x) implies
                exists|i: int| 0 <= i < need
                    && x.0 == self.id(#[trigger] srcs@[i] as int)
                    && x.1 == poss[i] && x.2 == msgs@[i] by {
                let i0 = choose|i: int| 0 <= i < srcs@.len()
                    && x == (ids0[srcs@[i] as int], poss[i], msgs@[i]);
                assert(self.id(srcs@[i0] as int) == ids0[srcs@[i0] as int]);
                assert(0 <= i0 < need
                    && x.0 == self.id(srcs@[i0] as int)
                    && x.1 == poss[i0] && x.2 == msgs@[i0]);
            }
        }
        (srcs, msgs, Tracked(cs), Ghost(poss))
    }

    /// Block until any peer sends, and report which. The interference point.
    pub fn recv_any(&mut self) -> (res: (usize, M))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).iid() == old(self).iid(),
            final(self).rxs@ == old(self).rxs@,
            final(self).ids@ == old(self).ids@,
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

/// Take one channel's two tokens out of the boot maps and open it.
///
/// A deployment holds the whole `sent` and `recvd` maps and hands out one
/// channel at a time; doing that by hand is three lines per channel and the
/// same three lines every time. The `remove`s and the ownership argument that
/// makes a second call impossible are `open_channel`'s, unchanged.
///
/// Verified, not trusted.
pub fn take_channel<M, Inv: NetInv<M>>(
    c: Ghost<ChanId>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(sm): Tracked<&mut MapToken<ChanId, Seq<M>, NetSM::sent<M, Inv>>>,
    Tracked(rm): Tracked<&mut MapToken<ChanId, Seq<M>, NetSM::recvd<M, Inv>>>,
) -> (res: (Out<M, Inv>, In<M, Inv>))
    requires
        old(sm).instance_id() == inst.id(), old(sm).dom().contains(c@),
        old(rm).instance_id() == inst.id(), old(rm).dom().contains(c@),
    ensures
        res.0.wf(), res.0.id() == c@, res.0.iid() == inst.id(),
        res.0.hist() == old(sm).map()[c@],
        res.1.wf(), res.1.id() == c@, res.1.iid() == inst.id(),
        final(sm).map() == old(sm).map().remove(c@),
        final(rm).map() == old(rm).map().remove(c@),
        final(sm).instance_id() == old(sm).instance_id(),
        final(rm).instance_id() == old(rm).instance_id(),
{
    let tracked stok;
    let tracked rtok;
    proof {
        stok = sm.remove(c@);
        rtok = rm.remove(c@);
    }
    open_channel::<M, Inv>(c, Tracked(inst), Tracked(stok), Tracked(rtok))
}

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
        &&& self.inbox.ids@ == self.h.chans()
    }
}

impl<M, Inv: NetInv<M>, H: NetHandler<M, Inv>> Process for Driven<M, Inv, H> {
    open spec fn wf(&self) -> bool { self.inv() }

    /// One turn: `N . L*`, then the single blocking receive, then `N . L*`.
    /// Repeating this is `(R . N . L*)*` -- a sequence of atomic blocks with a
    /// checked invariant between them, which is what `run` does.
    fn step(&mut self) {
        self.h.tick();
        let (k, m, Tracked(w)) = self.inbox.recv_any_wit();
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
