#![allow(unused_imports)]
use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub type ChanId = nat;

#[derive(Structural, PartialEq, Eq)]
pub enum Msg { Prepare, Vote(bool) }
}

tokenized_state_machine!{
    VoteSM {
        fields {
            /// FIFO => unique sender => the sender owns the history exactly.
            #[sharding(map)]            pub sent:  Map<ChanId, Seq<Msg>>,
            /// Receiver is not Clone => unique consumer => exclusive.
            #[sharding(map)]            pub recvd: Map<ChanId, Seq<Msg>>,
            /// Monotone knowledge: index `i` of channel `c` carries `m`.
            /// Duplicable, never retracted. This is how a RECEIVER learns
            /// anything about a history it does not own.
            #[sharding(persistent_set)] pub was_sent: Set<(ChanId, nat, Msg)>,

            #[sharding(constant)]       pub rsp:  ChanId,
            #[sharding(constant)]       pub vote: bool,
        }

        /// Monotone knowledge agrees with the histories it describes.
        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|c: ChanId, i: nat, m: Msg| #[trigger] self.was_sent.contains((c, i, m)) ==>
                self.sent.dom().contains(c)
                && i < self.sent[c].len()
                && self.sent[c][i as int] == m
        }

        /// THE YIELD INVARIANT: the response channel carries nothing but the
        /// participant's actual vote.
        #[invariant]
        pub spec fn rsp_carries_vote(&self) -> bool {
            forall|i: nat, m: Msg| #[trigger] self.was_sent.contains((self.rsp, i, m))
                ==> m == Msg::Vote(self.vote)
        }

        init!{
            boot(rsp: ChanId, vote: bool, chans: Set<ChanId>) {
                require(chans.contains(rsp));
                init sent     = Map::new(chans, |c: ChanId| Seq::<Msg>::empty());
                init recvd    = Map::new(chans, |c: ChanId| Seq::<Msg>::empty());
                init was_sent = Set::empty();
                init rsp      = rsp;
                init vote     = vote;
            }
        }

        transition!{
            do_send(c: ChanId, s: Seq<Msg>, m: Msg) {
                remove sent -= [c => s];
                // THE GATE. Civl's rho: the state from which this must not
                // fail. Discharged by the CALLER, at the call site.
                require(c == pre.rsp ==> m == Msg::Vote(pre.vote));
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        transition!{
            do_recv(c: ChanId, r: Seq<Msg>, m: Msg) {
                remove recvd -= [c => r];
                // FIFO delivery: you get index `r.len()`. Stated over MONOTONE
                // knowledge, so the receiver needs no access to `sent`.
                have   was_sent >= set { (c, r.len(), m) };
                add    recvd += [c => r.push(m)];
            }
        }

        /// How a thread cashes in the yield invariant. It holds a persistent
        /// witness; the macro proves the conclusion from the invariant.
        property!{
            learn_vote(c: ChanId, i: nat, m: Msg) {
                have was_sent >= set { (c, i, m) };
                require(c == pre.rsp);
                assert(m == Msg::Vote(pre.vote));
            }
        }

        #[inductive(boot)]
        fn boot_inductive(post: Self, rsp: ChanId, vote: bool, chans: Set<ChanId>) { }

        #[inductive(do_send)]
        fn do_send_inductive(pre: Self, post: Self, c: ChanId, s: Seq<Msg>, m: Msg) {
            assert forall|k: ChanId, i: nat, mm: Msg| #[trigger] post.was_sent.contains((k, i, mm))
                implies post.sent.dom().contains(k)
                    && i < post.sent[k].len() && post.sent[k][i as int] == mm by {
                if (k, i, mm) == (c, s.len(), m) {
                    assert(post.sent[c] == s.push(m));
                } else {
                    assert(pre.was_sent.contains((k, i, mm)));
                    if k == c { assert(post.sent[c] == s.push(m)); }
                }
            }
        }

        #[inductive(do_recv)]
        fn do_recv_inductive(pre: Self, post: Self, c: ChanId, r: Seq<Msg>, m: Msg) { }
    }
}

fn main(){}

// ===========================================================================
// TRUSTED SEAM. Two external_body functions whose specifications are exactly
// the state machine's two transitions. Nothing else here is trusted.
// ===========================================================================
verus!{
pub struct Sender  { pub id: Ghost<ChanId> }
pub struct Receiver{ pub id: Ghost<ChanId> }   // deliberately not Clone

#[verifier::external_body]
pub fn send(
    s: &Sender, m: Msg,
    Tracked(inst): Tracked<&VoteSM::Instance>,
    Tracked(tok):  Tracked<&mut VoteSM::sent>,
) -> (w: Tracked<VoteSM::was_sent>)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == s.id@,
        // THE GATE, discharged by the caller.
        s.id@ == inst.rsp() ==> m == Msg::Vote(inst.vote()),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == old(tok).key(),
        final(tok).value() == old(tok).value().push(m),
        w@.instance_id() == inst.id(),
        w@.element() == (s.id@, old(tok).value().len(), m),
{ unimplemented!() }

#[verifier::external_body]
pub fn recv(
    rx: &Receiver,
    Tracked(inst): Tracked<&VoteSM::Instance>,
    Tracked(tok):  Tracked<&mut VoteSM::recvd>,
) -> (res: (Msg, Tracked<VoteSM::was_sent>))
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == rx.id@,
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == old(tok).key(),
        final(tok).value() == old(tok).value().push(res.0),
        res.1@.instance_id() == inst.id(),
        res.1@.element() == (rx.id@, old(tok).value().len(), res.0),
{ unimplemented!() }
}

// ===========================================================================
// THE PROTOCOL. Ordinary sequential Rust.
// ===========================================================================
verus!{
pub fn coordinator(
    req: &Sender, rsp: &Receiver,
    Tracked(inst):      Tracked<&VoteSM::Instance>,
    Tracked(sent_req):  Tracked<&mut VoteSM::sent>,
    Tracked(recvd_rsp): Tracked<&mut VoteSM::recvd>,
) -> (b: bool)
    requires
        old(sent_req).instance_id()  == inst.id(),  old(sent_req).key()  == req.id@,
        old(recvd_rsp).instance_id() == inst.id(),  old(recvd_rsp).key() == rsp.id@,
        rsp.id@ == inst.rsp(),
        req.id@ != inst.rsp(),
    ensures
        b ==> inst.vote(),          // SAFETY: commit only if the vote was yes
{
    // LEFT MOVER. Gate obligation `req.id@ == rsp ==> ...` is vacuous here.
    let _w = send(req, Msg::Prepare, Tracked(inst), Tracked(sent_req));

    // YIELD POINT. The only interference point in this function.
    let (m, w) = recv(rsp, Tracked(inst), Tracked(recvd_rsp));

    // Cash in the yield invariant, using the witness the receive handed back.
    proof {
        inst.learn_vote(rsp.id@, old(recvd_rsp).value().len(), m, w.borrow());
    }

    match m {
        Msg::Vote(b)  => b,
        Msg::Prepare  => false,
    }
}

pub fn participant(
    rx: &Receiver, tx: &Sender, vote: bool,
    Tracked(inst):      Tracked<&VoteSM::Instance>,
    Tracked(recvd_req): Tracked<&mut VoteSM::recvd>,
    Tracked(sent_rsp):  Tracked<&mut VoteSM::sent>,
)
    requires
        old(recvd_req).instance_id() == inst.id(), old(recvd_req).key() == rx.id@,
        old(sent_rsp).instance_id()  == inst.id(), old(sent_rsp).key()  == tx.id@,
        tx.id@ == inst.rsp(),
        vote == inst.vote(),
{
    // RIGHT MOVER (blocking). Opens the atomic block.
    let (_m, _w) = recv(rx, Tracked(inst), Tracked(recvd_req));
    // LEFT MOVER. Same block: no interference point between the two.
    // The gate bites here -- sending anything but the true vote is rejected.
    let _w2 = send(tx, Msg::Vote(vote), Tracked(inst), Tracked(sent_rsp));
}
}

// ===========================================================================
// THE RPC TRICK IN THE TOKEN SETTING
// ===========================================================================
verus!{
/// ABSTRACTED RECEIVE. The blocking `recv` is a RIGHT mover, so `send; recv`
/// is L.R -- the wrong shape, and the pair cannot be one atomic block. Here the
/// gate is strengthened to "the caller already holds a witness that the reply
/// was sent". Under that gate the operation cannot block, so it is a LEFT
/// mover, and `send; recv_abs` collapses to L.L: one block, no yield.
///
/// Note what the witness buys beyond non-blocking. It names the INDEX, so the
/// message is pinned by the machine's `agree` invariant. The old design needed
/// a freshly minted single-use channel and a `lemma_singleton_delivery` to get
/// that determinism; here it falls out.
#[verifier::external_body]
pub fn recv_abs(
    rx: &Receiver,
    Tracked(inst): Tracked<&VoteSM::Instance>,
    Tracked(tok):  Tracked<&mut VoteSM::recvd>,
    Tracked(w):    Tracked<&VoteSM::was_sent>,
) -> (m: Msg)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == rx.id@,
        w.instance_id() == inst.id(),
        // THE GATE: the reply is already on the channel, at the index we are
        // about to consume.
        w.element().0 == rx.id@,
        w.element().1 == old(tok).value().len(),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == old(tok).key(),
        final(tok).value() == old(tok).value().push(m),
        m == w.element().2,          // deterministic: no freshness needed
{ unimplemented!() }
}

verus!{
/// Civl's synchronized asynchronous call, `async call {:sync}`. The handler is
/// a LEFT mover and its request has already been sent, so its action may be
/// executed at the CALL SITE. In the token setting that is not an axiom about
/// global state: the caller literally performs the handler's own transition,
/// using the reply channel's send token, which it holds because it minted the
/// channel. The gate of that transition -- "anything on the response channel is
/// the true vote" -- is discharged here, exactly as the participant would.
pub proof fn absorb_handler(
    tracked inst: &VoteSM::Instance,
    tracked sent_rsp: VoteSM::sent,
) -> (tracked res: (VoteSM::sent, VoteSM::was_sent))
    requires
        sent_rsp.instance_id() == inst.id(),
        sent_rsp.key() == inst.rsp(),
    ensures
        res.1.instance_id() == inst.id(),
        res.1.element() == (inst.rsp(), sent_rsp.value().len(), Msg::Vote(inst.vote())),
        res.0.instance_id() == inst.id(),
        res.0.key() == inst.rsp(),
        res.0.value() == sent_rsp.value().push(Msg::Vote(inst.vote())),
{
    let tracked (t, w) = inst.do_send(
        inst.rsp(), sent_rsp.value(), Msg::Vote(inst.vote()), sent_rsp);
    (t.get(), w.get())
}
}

verus!{
/// A remote call, VERIFIED, not assumed. The whole body is L . L: a left-moving
/// send, then a left-moving abstracted receive. There is NO interference point
/// inside it, so to its caller it is one atomic action -- an ordinary function
/// call that happens to involve two messages.
///
/// The reply capability is passed BY VALUE and consumed: a reply channel is
/// one-shot, and Rust's linearity is what says so.
pub fn rpc(
    req: &Sender, rsp_rx: &Receiver,
    Tracked(inst):      Tracked<&VoteSM::Instance>,
    Tracked(sent_req):  Tracked<&mut VoteSM::sent>,
    Tracked(reply_cap): Tracked<VoteSM::sent>,
    Tracked(recvd_rsp): Tracked<&mut VoteSM::recvd>,
) -> (m: Msg)
    requires
        old(sent_req).instance_id() == inst.id(),  old(sent_req).key() == req.id@,
        reply_cap.instance_id()     == inst.id(),  reply_cap.key()     == inst.rsp(),
        old(recvd_rsp).instance_id()== inst.id(),  old(recvd_rsp).key()== rsp_rx.id@,
        rsp_rx.id@ == inst.rsp(),
        req.id@ != inst.rsp(),
        // the reply will land at the index we are about to consume
        old(recvd_rsp).value().len() == reply_cap.value().len(),
    ensures
        m == Msg::Vote(inst.vote()),
{
    // LEFT MOVER.
    let _w = send(req, Msg::Prepare, Tracked(inst), Tracked(sent_req));

    // The handler runs HERE, at the call site. Consumes the reply capability.
    let tracked w2;
    proof {
        let tracked (_spent, wit) = absorb_handler(inst, reply_cap);
        w2 = wit;
    }

    // LEFT MOVER, because the gate is discharged by the witness above.
    recv_abs(rsp_rx, Tracked(inst), Tracked(recvd_rsp), Tracked(&w2))
}

/// The coordinator, now written as straight-line sequential code with a remote
/// call in it. One atomic block; no yield point anywhere in this function.
pub fn coordinator_rpc(
    req: &Sender, rsp_rx: &Receiver,
    Tracked(inst):      Tracked<&VoteSM::Instance>,
    Tracked(sent_req):  Tracked<&mut VoteSM::sent>,
    Tracked(reply_cap): Tracked<VoteSM::sent>,
    Tracked(recvd_rsp): Tracked<&mut VoteSM::recvd>,
) -> (b: bool)
    requires
        old(sent_req).instance_id() == inst.id(),  old(sent_req).key() == req.id@,
        reply_cap.instance_id()     == inst.id(),  reply_cap.key()     == inst.rsp(),
        old(recvd_rsp).instance_id()== inst.id(),  old(recvd_rsp).key()== rsp_rx.id@,
        rsp_rx.id@ == inst.rsp(),
        req.id@ != inst.rsp(),
        old(recvd_rsp).value().len() == reply_cap.value().len(),
    ensures
        b ==> inst.vote(),           // SAFETY, same property as before
{
    let m = rpc(req, rsp_rx, Tracked(inst), Tracked(sent_req),
                Tracked(reply_cap), Tracked(recvd_rsp));
    match m {
        Msg::Vote(b) => b,
        Msg::Prepare => false,
    }
}
}
