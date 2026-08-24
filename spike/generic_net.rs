#![allow(unused_imports)]
// Can the network state machine live in the LIBRARY, parameterised by the
// protocol, instead of being generated per protocol?
//
// If a trait can supply the gate, the message guarantee and the delivery
// discipline, and those can be called from inside `tokenized_state_machine!`,
// then there is one machine for all protocols and no macro at all.
use vstd::prelude::*;
use core::marker::PhantomData;
use vstd::tokens::{InstanceId, KeyValueToken, ElementToken};
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub type ChanId = nat;

/// Everything a protocol has to say about its messages.
pub trait NetInv<M> : Sized {
    /// The states from which a send must not fail.
    spec fn gate(c: ChanId, s: Seq<M>, m: M) -> bool;
    /// What is guaranteed about a message that was sent.
    spec fn wit_inv(c: ChanId, m: M) -> bool;
    /// Which index may be delivered next.
    spec fn deliverable_at(v: Seq<M>, i: nat) -> bool;

    /// An additional invariant over the send histories, for guarantees that a
    /// single message cannot express -- an ordering between messages, say.
    /// Most protocols leave this `true`.
    spec fn extra(sent: Map<ChanId, Seq<M>>) -> bool;

    /// The one obligation: the gate is strong enough to establish the
    /// guarantee for the message it admits.
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<M>, m: M)
        requires Self::gate(c, s, m)
        ensures  Self::wit_inv(c, m);

    /// The additional invariant holds of the initial state.
    proof fn lemma_extra_init(chans: Set<ChanId>)
        ensures Self::extra(Map::new(chans, |c: ChanId| Seq::<M>::empty()));

    /// ... and to preserve the additional invariant.
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<M>>, c: ChanId, s: Seq<M>, m: M)
        requires
            Self::extra(sent), Self::gate(c, s, m),
            sent.dom().contains(c), sent[c] == s,
        ensures
            Self::extra(sent.insert(c, s.push(m)));
}
}

tokenized_state_machine!{
    NetSM<M, Inv: NetInv<M>> {
        fields {
            #[sharding(map)]            pub sent:  Map<ChanId, Seq<M>>,
            #[sharding(map)]            pub recvd: Map<ChanId, Seq<M>>,
            #[sharding(persistent_set)] pub was_sent: Set<(ChanId, nat, M)>,
            #[sharding(variable)]       pub next: nat,
            /// Carries the protocol parameter; see `rwlock.rs` for the idiom.
            #[sharding(constant)]       pub inv: PhantomData<Inv>,
        }

        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|c: ChanId, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> self.sent.dom().contains(c)
                    && i < self.sent[c].len() && self.sent[c][i as int] == m
        }

        /// The protocol's guarantee, applied through the type parameter.
        #[invariant]
        pub spec fn protocol_extra(&self) -> bool { Inv::extra(self.sent) }

        #[invariant]
        pub spec fn protocol_inv(&self) -> bool {
            forall|c: ChanId, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> Inv::wit_inv(c, m)
        }

        init!{
            boot(chans: Set<ChanId>) {
                init sent     = Map::new(chans, |c: ChanId| Seq::<M>::empty());
                init recvd    = Map::new(chans, |c: ChanId| Seq::<M>::empty());
                init was_sent = Set::empty();
                init next     = 0;
                init inv      = PhantomData;
            }
        }

        transition!{
            do_send(c: ChanId, s: Seq<M>, m: M) {
                remove sent -= [c => s];
                require(Inv::gate(c, s, m));            // the protocol's gate
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        transition!{
            do_recv(c: ChanId, r: Seq<M>, i: nat, m: M) {
                remove recvd -= [c => r];
                have   was_sent >= set { (c, i, m) };
                require(Inv::deliverable_at(r, i));     // the protocol's discipline
                add    recvd += [c => r.push(m)];
            }
        }

        property!{
            learn(c: ChanId, i: nat, m: M) {
                have was_sent >= set { (c, i, m) };
                assert(Inv::wit_inv(c, m));
            }
        }

        #[inductive(boot)]
        fn boot_inductive(post: Self, chans: Set<ChanId>) {
            Inv::lemma_extra_init(chans);
        }

        #[inductive(do_send)]
        fn do_send_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, m: M) {
            Inv::lemma_gate_gives_inv(c, s, m);
            assert(pre.sent.dom().contains(c));
            assert(pre.sent[c] == s);
            Inv::lemma_extra_preserved(pre.sent, c, s, m);
            assert(post.sent =~= pre.sent.insert(c, s.push(m)));
            assert(Inv::extra(post.sent));
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                implies post.sent.dom().contains(k)
                    && i < post.sent[k].len() && post.sent[k][i as int] == mm by {
                if (k, i, mm) != (c, s.len(), m) { assert(pre.was_sent.contains((k, i, mm))); }
                if k == c { assert(post.sent[c] == s.push(m)); }
            }
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                implies Inv::wit_inv(k, mm) by {
                if (k, i, mm) != (c, s.len(), m) { assert(pre.was_sent.contains((k, i, mm))); }
            }
        }

        #[inductive(do_recv)]
        fn do_recv_inductive(pre: Self, post: Self, c: ChanId, r: Seq<M>, i: nat, m: M) { }
    }
}

verus!{
// A protocol is now just this.
pub struct Pkt { pub v: u64 }
pub uninterp spec fn ok(v: u64) -> bool;
pub uninterp spec fn link() -> ChanId;

pub struct Lossy;

impl NetInv<Pkt> for Lossy {
    open spec fn gate(c: ChanId, s: Seq<Pkt>, m: Pkt) -> bool { c == link() ==> ok(m.v) }
    open spec fn wit_inv(c: ChanId, m: Pkt) -> bool { c == link() ==> ok(m.v) }
    open spec fn deliverable_at(v: Seq<Pkt>, i: nat) -> bool { true }
    open spec fn extra(sent: Map<ChanId, Seq<Pkt>>) -> bool { true }
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Pkt>, m: Pkt) { }
    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<Pkt>>, c: ChanId,
                                   s: Seq<Pkt>, m: Pkt) { }
}
}
fn main(){}

verus!{
/// A protocol whose guarantee is about PAIRS of messages, which `wit_inv`
/// cannot express. It uses `extra` and nothing else changes.
pub struct Beats;
pub uninterp spec fn beat_link() -> ChanId;

impl NetInv<Pkt> for Beats {
    open spec fn gate(c: ChanId, s: Seq<Pkt>, m: Pkt) -> bool {
        forall|x: int| 0 <= x < s.len() ==> (#[trigger] s[x]).v < m.v
    }
    open spec fn wit_inv(c: ChanId, m: Pkt) -> bool { true }
    open spec fn deliverable_at(v: Seq<Pkt>, i: nat) -> bool { i == v.len() }

    open spec fn extra(sent: Map<ChanId, Seq<Pkt>>) -> bool {
        sent.dom().contains(beat_link()) ==>
            forall|x: int, y: int| 0 <= x < y < sent[beat_link()].len()
                ==> (#[trigger] sent[beat_link()][x]).v < (#[trigger] sent[beat_link()][y]).v
    }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Pkt>, m: Pkt) { }

    proof fn lemma_extra_init(chans: Set<ChanId>) {
        let s0 = Map::new(chans, |c: ChanId| Seq::<Pkt>::empty());
        if s0.dom().contains(beat_link()) { assert(s0[beat_link()].len() == 0); }
    }

    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<Pkt>>, c: ChanId,
                                   s: Seq<Pkt>, m: Pkt) {
        let post = sent.insert(c, s.push(m));
        if post.dom().contains(beat_link()) {
            assert forall|x: int, y: int| 0 <= x < y < post[beat_link()].len()
                implies (#[trigger] post[beat_link()][x]).v
                      < (#[trigger] post[beat_link()][y]).v by {
                if c == beat_link() { assert(post[beat_link()] == s.push(m)); }
            }
        }
    }
}
}

verus!{
// What do the generated token types look like for a generic machine?
pub struct Sender<M> { pub id: Ghost<ChanId>, pub p: core::marker::PhantomData<M> }

#[verifier::external_body]
pub fn gsend<M, Inv: NetInv<M>>(
    s: &Sender<M>, m: M,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):  Tracked<&mut NetSM::sent<M, Inv>>,
) -> (w: Tracked<NetSM::was_sent<M, Inv>>)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == s.id@,
        Inv::gate(s.id@, old(tok).value(), m),
    ensures
        final(tok).value() == old(tok).value().push(m),
        w@.element() == (s.id@, old(tok).value().len(), m),
{ unimplemented!() }
}
