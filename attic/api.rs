// Thread-side API. TRUSTED: everything `external_body` here is the trust
// boundary. Soundness rests on the reduction meta-theory, which Verus does not
// and cannot check.

use vstd::prelude::*;
use crate::net::*;
pub use crate::layer::Spec;
pub use crate::tok::{Sender, Receiver};

verus! {

/// Everything a protocol must declare: its message type, its channel
/// semantics, its yield invariant, and its complete ACTION POOL.
///
/// Bundling these means a thread's `NetToken<P>` fixes which protocol it is
/// running. A thread cannot accidentally justify a non-yielding operation
/// against some other protocol's pool -- that is now a type error.
///
/// Completeness of `A` -- that it really enumerates every action of the
/// protocol -- remains a MODELLING obligation, discharged by review.
/// THE BOTTOM LAYER: a `Spec` whose state is the network, carrying in addition
/// everything that only makes sense there -- the channel discipline, footprints,
/// and the mover obligations that justify reduction.
pub trait Protocol : Spec<S = Net<<Self as Spec>::M>> {
    /// Channel semantics (per-link FIFO, or bag).
    type C: ChannelModel<Self::M>;

    /// Consuming a message cannot break an invariant over send histories.
    proof fn lemma_recv_preserves(net: Net<Self::M>, c: ChanId, m: Self::M)
        requires Self::inv(net)
        ensures  Self::inv(net.do_recv(c, m));

    // ---- action pool -----------------------------------------------------

    /// The channels an action may read or write.
    spec fn footprint(a: Self::A, req: Self::M) -> Set<ChanId>;

    /// FRAMING: an action does not WRITE outside its footprint.
    proof fn lemma_frame(a: Self::A, req: Self::M, resp: Self::M,
                         n0: Net<Self::M>, n1: Net<Self::M>)
        requires Self::gate(a, req, n0), Self::step(a, req, resp, n0, n1)
        ensures
            n0.dom().subset_of(n1.dom()),
            forall|c: ChanId| !Self::footprint(a, req).contains(c)
                ==> #[trigger] n1.chans[c] == n0.chans[c];

    /// NON-INTERFERENCE: every action preserves the yield invariant.
    proof fn lemma_preserves_inv(a: Self::A, req: Self::M, resp: Self::M,
                                 n0: Net<Self::M>, n1: Net<Self::M>)
        requires Self::gate(a, req, n0), Self::step(a, req, resp, n0, n1), Self::inv(n0)
        ensures  Self::inv(n1);

    /// LOCALITY (send): an action does not READ outside its footprint either,
    /// so an unrelated append neither enables, disables, nor alters it.
    /// THIS IS EXACTLY "send is a left mover w.r.t. this action".
    proof fn lemma_local_send(a: Self::A, req: Self::M, resp: Self::M,
                              n0: Net<Self::M>, n1: Net<Self::M>, c: ChanId, m: Self::M)
        requires
            Self::gate(a, req, n0), Self::step(a, req, resp, n0, n1),
            !Self::footprint(a, req).contains(c)
        ensures
            Self::step(a, req, resp, n0.do_send(c, m), n1.do_send(c, m)),
            // LEFT-MOVER CONDITION (1): the gate is forward-preserved.
            Self::gate(a, req, n0.do_send(c, m));

    /// LOCALITY (receive): the dual, justifying the non-yielding `recv_abs`.
    proof fn lemma_local_recv(a: Self::A, req: Self::M, resp: Self::M,
                              n0: Net<Self::M>, n1: Net<Self::M>, c: ChanId, m: Self::M)
        requires
            Self::gate(a, req, n0), Self::step(a, req, resp, n0, n1),
            !Self::footprint(a, req).contains(c)
        ensures
            Self::step(a, req, resp, n0.do_recv(c, m), n1.do_recv(c, m)),
            // LEFT-MOVER CONDITION (2): the gate is backward-preserved.
            Self::gate(a, req, n0.do_recv(c, m));

    /// PAIRWISE COMMUTATIVITY: disjoint-footprint actions commute. Stated
    /// EXISTENTIALLY, as Civl does -- every `a; b` execution can be reordered
    /// into a `b; a` execution reaching the same final state. A universally
    /// quantified `nab == nba` would be unprovable for nondeterministic
    /// actions, and abstract layers are inherently nondeterministic.
    proof fn lemma_commutes(
        a: Self::A, b: Self::A, ra: Self::M, rb: Self::M, sa: Self::M, sb: Self::M,
        n0: Net<Self::M>, mid_ab: Net<Self::M>, nab: Net<Self::M>,
    )
        requires
            Self::footprint(a, ra).disjoint(Self::footprint(b, rb)),
            Self::gate(a, ra, n0), Self::gate(b, rb, n0),
            Self::step(a, ra, sa, n0, mid_ab),
            Self::step(b, rb, sb, mid_ab, nab),
        ensures
            exists|mid: Net<Self::M>|
                Self::step(b, rb, sb, n0, mid) && Self::step(a, ra, sa, mid, nab);
}

/// One thread's view of the network, plus the endpoint ownership it holds.
/// The `P` parameter pins the protocol: every non-yielding operation on this
/// token is justified against `P`'s pool, and no other.
pub struct NetToken<P: Protocol> {
    pub net: Net<P::M>,
    pub send_owned: Set<ChanId>,
    pub recv_owned: Set<ChanId>,
    pub p: core::marker::PhantomData<P>,
}

/// How the network may evolve underneath a thread, ignoring ownership
/// bookkeeping. Factored out of `env_step` because thread forking changes a
/// thread's ownership while the network still only advances.
pub open spec fn net_advances<P: Protocol>(t0: NetToken<P>, t1: NetToken<P>) -> bool {
    &&& t0.net.dom().subset_of(t1.net.dom())
    // MONOTONICITY: send histories only ever grow.
    &&& forall|c: ChanId| t0.net.dom().contains(c)
          ==> #[trigger] t0.net.sent(c).is_prefix_of(t1.net.sent(c))
    // FRAMING FROM OWNERSHIP: unique sender => nobody else appends.
    &&& forall|c: ChanId| t0.net.dom().contains(c) && t0.send_owned.contains(c)
          ==> #[trigger] t1.net.sent(c) == t0.net.sent(c)
    // FRAMING FROM OWNERSHIP: unique consumer => nobody else consumes.
    &&& forall|c: ChanId| t0.net.dom().contains(c) && t0.recv_owned.contains(c)
          ==> #[trigger] t1.net.recvd(c) == t0.net.recvd(c)
    &&& forall|c: ChanId| t0.net.dom().contains(c) && !t0.recv_owned.contains(c)
          ==> #[trigger] t0.net.recvd(c).is_prefix_of(t1.net.recvd(c))
}

/// What the environment may do while this thread is at a yield point. The
/// thread's own ownership is untouched; only the network moves.
pub open spec fn env_step<P: Protocol>(t0: NetToken<P>, t1: NetToken<P>) -> bool {
    &&& t1.send_owned == t0.send_owned
    &&& t1.recv_owned == t0.recv_owned
    &&& net_advances(t0, t1)
}

// ---------------------------------------------------------------------------
// PROCESSES WITH SEVERAL THREADS
// ---------------------------------------------------------------------------
//
// A "thread" above is really a unit of sequential control that owns endpoints.
// A process in a distributed system usually has several: the 2PC coordinator
// naturally spawns one thread per participant. Nothing in the model forces
// those threads to be separate processes -- they are just more threads, and the
// yield invariant already tolerates arbitrary interference from any of them.
//
// What has to be added is the ability to DIVIDE a token, because ownership is
// what makes the framing clauses of `env_step` sound. `send_owned` means "this
// thread is the only sender", so it may be handed to at most one sibling.
// Splitting into disjoint halves preserves exactly that reading; merging on
// join puts the halves back together.
//
// Both are TRUSTED. Their justification is bookkeeping, not protocol
// reasoning: a permission that names one holder still names one holder after it
// has been moved.

/// TRUSTED. Divide a token for two sibling threads. Channels in `s1`/`r1` go to
/// the first half, the rest to the second. Both halves start from the same view
/// of the network and evolve it independently, exactly as unrelated threads do.
#[verifier::external_body]
pub proof fn split_token<P: Protocol>(tracked t: NetToken<P>, s1: Set<ChanId>, r1: Set<ChanId>)
    -> (tracked res: (NetToken<P>, NetToken<P>))
    ensures
        res.0.net == t.net,
        res.1.net == t.net,
        res.0.send_owned == t.send_owned.intersect(s1),
        res.1.send_owned == t.send_owned.difference(s1),
        res.0.recv_owned == t.recv_owned.intersect(r1),
        res.1.recv_owned == t.recv_owned.difference(r1),
{
    unimplemented!()
}

/// TRUSTED. Recombine two sibling tokens at a join. The result owns the union,
/// which is well defined precisely because the halves were disjoint. Its view
/// of the network is a common successor of both halves' views: each half's
/// exclusively owned channels are still framed, because the only other holder
/// was the other half, and it owned none of them.
///
/// The invariant carries across because every action of `P` preserves it --
/// that is the `lemma_preserves_inv` obligation -- so any state reachable by
/// interleaving the two halves satisfies it.
#[verifier::external_body]
pub proof fn merge_token<P: Protocol>(tracked a: NetToken<P>, tracked b: NetToken<P>)
    -> (tracked res: NetToken<P>)
    requires
        a.send_owned.disjoint(b.send_owned),
        a.recv_owned.disjoint(b.recv_owned),
        P::inv(a.net),
        P::inv(b.net),
    ensures
        res.send_owned == a.send_owned.union(b.send_owned),
        res.recv_owned == a.recv_owned.union(b.recv_owned),
        net_advances(a, res),
        net_advances(b, res),
        P::inv(res.net),
{
    unimplemented!()
}

// ---------------------------------------------------------------------------
// TRUSTED API
// ---------------------------------------------------------------------------

/// Nonblocking send. LEFT MOVER w.r.t. `P`'s pool, so it is *not* a yield
/// point: reduction lets the following code stay in the same atomic block.
///
/// NOTE the absence of an invariant obligation here. `P::inv` is required at
/// YIELD POINTS (`recv`, `yield_point`) and preserved per ACTION
/// (`lemma_preserves_inv`), which is a whole reduced block. Demanding it at
/// each individual send would be strictly stronger than reduction needs, and
/// would reject any action that transiently breaks the invariant between two of
/// its own sends. Nobody can observe those intermediate states: that is what
/// atomicity of the block means.
#[verifier::external_body]
pub fn send<P: Protocol>(s: &Sender<P::M>, m: P::M, Tracked(t): Tracked<&mut NetToken<P>>)
    requires
        old(t).net.dom().contains(s.id@),
    ensures
        final(t).net == old(t).net.do_send(s.id@, m),
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned,
{
    unimplemented!()
}

/// Blocking receive at a yield point. RIGHT MOVER, and blocking, so the
/// environment runs first: the postcondition gives `env_step` then delivery.
#[verifier::external_body]
pub fn recv<P: Protocol>(r: &Receiver<P::M>, Tracked(t): Tracked<&mut NetToken<P>>) -> (m: P::M)
    requires
        old(t).net.dom().contains(r.id@),
        old(t).recv_owned.contains(r.id@),
        P::inv(old(t).net),
    ensures
        exists|mid: NetToken<P>|
            env_step(*old(t), mid) && P::inv(mid.net)
            && P::C::deliverable(mid.net.sent(r.id@), mid.net.recvd(r.id@), m)
            && final(t).net == mid.net.do_recv(r.id@, m),
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned,
        final(t).net.dom().contains(r.id@),
{
    unimplemented!()
}

/// ABSTRACTED receive: gate strengthened to "a message is already present".
/// Given that gate it never blocks, hence it is a LEFT mover, hence it does not
/// yield and can sit inside an atomic block after a `send`. This is Civl's
/// `CollectAbs` abstraction, and it is what makes RPC look like a call.
#[verifier::external_body]
pub fn recv_abs<P: Protocol>(r: &Receiver<P::M>, Tracked(t): Tracked<&mut NetToken<P>>)
    -> (m: P::M)
    requires
        old(t).net.dom().contains(r.id@),
        old(t).recv_owned.contains(r.id@),
        // THE GATE. Discharging this is the caller's proof obligation.
        old(t).net.recvd(r.id@).len() < old(t).net.sent(r.id@).len(),
    ensures
        P::C::deliverable(old(t).net.sent(r.id@), old(t).net.recvd(r.id@), m),
        final(t).net == old(t).net.do_recv(r.id@, m),
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned,
{
    unimplemented!()
}

/// Explicit yield point.
#[verifier::external_body]
pub fn yield_point<P: Protocol>(Tracked(t): Tracked<&mut NetToken<P>>)
    requires P::inv(old(t).net),
    ensures  env_step(*old(t), *final(t)), P::inv(final(t).net),
{
    unimplemented!()
}

/// Allocate a fresh single-use reply channel. The returned `Receiver` is added
/// to `recv_owned`; the `Sender` is meant to be moved into a request message.
#[verifier::external_body]
pub fn oneshot<P: Protocol>(Tracked(t): Tracked<&mut NetToken<P>>)
    -> (res: (Sender<P::M>, Receiver<P::M>))
    ensures
        !old(t).net.dom().contains(res.0.id@),
        res.0.id@ == res.1.id@,
        final(t).net.dom() == old(t).net.dom().insert(res.0.id@),
        final(t).net.chans[res.0.id@]
            == (Chan::<P::M> { sent: Seq::empty(), recvd: Seq::empty() }),
        forall|c: ChanId| old(t).net.dom().contains(c)
            ==> #[trigger] final(t).net.chans[c] == old(t).net.chans[c],
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned.insert(res.0.id@),
{
    unimplemented!()
}

/// A handler is a distinguished MEMBER of a protocol's pool.
pub trait Handler<P: Protocol> : Sized {
    /// Which pool action this handler is.
    spec fn me() -> P::A;

    /// The channel it replies on.
    spec fn reply_chan(req: P::M) -> ChanId;

    /// The reply channel is inside the footprint, so a disjoint-footprint
    /// action provably cannot forge or consume this handler's reply.
    proof fn lemma_reply_in_footprint(req: P::M)
        ensures P::footprint(Self::me(), req).contains(Self::reply_chan(req));

    /// LEFT-MOVER CONDITION (4): non-blocking.
    proof fn lemma_nonblocking(req: P::M, n0: Net<P::M>)
        requires P::inv(n0), P::gate(Self::me(), req, n0)
        ensures  exists|resp: P::M, n1: Net<P::M>| P::step(Self::me(), req, resp, n0, n1);

    /// Effect on the reply channel is exactly one append.
    proof fn lemma_reply_effect(req: P::M, resp: P::M, n0: Net<P::M>, n1: Net<P::M>)
        requires
            P::gate(Self::me(), req, n0),
            P::step(Self::me(), req, resp, n0, n1),
            n0.dom().contains(Self::reply_chan(req))
        ensures
            n1.sent(Self::reply_chan(req)) == n0.sent(Self::reply_chan(req)).push(resp),
            n1.recvd(Self::reply_chan(req)) == n0.recvd(Self::reply_chan(req));
}

/// THE ONLY REMAINING AXIOM. A left-moving handler whose request has already
/// been sent may be executed immediately at the call site, because a left mover
/// commutes leftwards until it abuts its caller. This is Civl's
/// `async call {:sync}` rule, stated once and for all.
///
/// What stays trusted is Lipton's theorem itself -- that pairwise commutativity
/// licenses the reordering -- not any claim about a particular protocol.
#[verifier::external_body]
pub proof fn absorb_handler<P: Protocol, H: Handler<P>>(
    tracked t: &mut NetToken<P>, req: P::M,
) -> (resp: P::M)
    requires
        P::inv(old(t).net),
        P::gate(H::me(), req, old(t).net),
        old(t).net.dom().contains(H::reply_chan(req)),
    ensures
        P::step(H::me(), req, resp, old(t).net, final(t).net),
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned,
{
    unimplemented!()
}

/// TIER-1 RPC. A VERIFIED FUNCTION: send the request (left mover, no yield),
/// absorb the handler, then `recv_abs` whose gate is now discharged because the
/// reply provably exists.
pub fn rpc<P: Protocol, H: Handler<P>>(
    tx: &Sender<P::M>, req: P::M, rx: &Receiver<P::M>, Tracked(t): Tracked<&mut NetToken<P>>,
) -> (resp: P::M)
    requires
        old(t).net.dom().contains(tx.id@),
        old(t).net.dom().contains(rx.id@),
        old(t).recv_owned.contains(rx.id@),
        tx.id@ != rx.id@,
        // `rx` really is this call's private, freshly-minted reply channel.
        rx.id@ == H::reply_chan(req),
        old(t).net.sent(rx.id@) == Seq::<P::M>::empty(),
        old(t).net.recvd(rx.id@) == Seq::<P::M>::empty(),
        P::inv(old(t).net.do_send(tx.id@, req)),
        P::gate(H::me(), req, old(t).net.do_send(tx.id@, req)),
    ensures
        exists|n2: Net<P::M>|
            P::step(H::me(), req, resp, old(t).net.do_send(tx.id@, req), n2)
            && final(t).net == n2.do_recv(rx.id@, resp),
        final(t).send_owned == old(t).send_owned,
        final(t).recv_owned == old(t).recv_owned,
        P::inv(final(t).net),
{
    let ghost g_req = req;
    let ghost rid = rx.id@;
    proof { lemma_do_send_dom(t.net, tx.id@, g_req); }

    send::<P>(tx, req, Tracked(t));

    let ghost n1 = t.net;
    let ghost g_resp = absorb_handler::<P, H>(t, g_req);
    proof {
        P::lemma_frame(H::me(), g_req, g_resp, n1, t.net);
        H::lemma_reply_effect(g_req, g_resp, n1, t.net);
        P::lemma_preserves_inv(H::me(), g_req, g_resp, n1, t.net);
        assert(t.net.sent(rid) =~= Seq::<P::M>::empty().push(g_resp));
    }

    let ghost n2 = t.net;
    proof { P::lemma_recv_preserves(n2, rid, g_resp); }
    let resp = recv_abs::<P>(rx, Tracked(t));
    proof {
        P::C::lemma_singleton_delivery(n2.sent(rid), resp, g_resp);
        assert(resp == g_resp);
        P::lemma_recv_preserves(n2, rid, resp);
    }
    resp
}

} // verus!
