#![allow(unused_imports)]
// Can a send require PROVENANCE: that some other message was already sent on
// some other channel, evidenced by a witness the sender presents?
use vstd::prelude::*;
use vstd::tokens::{InstanceId, KeyValueToken, ElementToken};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub type ChanId = nat;

pub trait Prov<M> : Sized {
    spec fn gate(c: ChanId, s: Seq<M>, m: M) -> bool;
    /// Does sending `m` on `c` require pointing at an earlier message?
    spec fn needs_cause(c: ChanId, m: M) -> bool;
    /// Is `m2` on `d` acceptable provenance for `m` on `c`?
    spec fn caused_ok(c: ChanId, m: M, d: ChanId, m2: M) -> bool;
}
}

tokenized_state_machine!{
    ProvSM<M, Inv: Prov<M>> {
        fields {
            #[sharding(map)]            pub sent: Map<ChanId, Seq<M>>,
            #[sharding(persistent_set)] pub was_sent: Set<(ChanId, nat, M)>,
            #[sharding(constant)]       pub inv: PhantomData<Inv>,
        }

        /// Every message that needs provenance has it. The existential ranges
        /// over `was_sent`, which only grows, so this is stable under any
        /// interference: no thread can remove the justification.
        #[invariant]
        pub spec fn provenance(&self) -> bool {
            forall|c: ChanId, i: nat, m: M|
                (#[trigger] self.was_sent.contains((c, i, m))) && Inv::needs_cause(c, m)
                    ==> exists|d: ChanId, j: nat, m2: M|
                            self.was_sent.contains((d, j, m2)) && Inv::caused_ok(c, m, d, m2)
        }

        init!{
            boot(chans: Set<ChanId>) {
                init sent = Map::new(chans, |c: ChanId| Seq::<M>::empty());
                init was_sent = Set::empty();
                init inv = PhantomData;
            }
        }

        /// A message that needs no earlier cause.
        transition!{
            do_send(c: ChanId, s: Seq<M>, m: M) {
                remove sent -= [c => s];
                require(Inv::gate(c, s, m) && !Inv::needs_cause(c, m));
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        /// A message justified by one already sent. The `have` is what forces
        /// the sender to actually hold the witness.
        transition!{
            do_send_caused(c: ChanId, s: Seq<M>, m: M, d: ChanId, j: nat, m2: M) {
                remove sent -= [c => s];
                require(Inv::gate(c, s, m) && Inv::caused_ok(c, m, d, m2));
                have   was_sent >= set { (d, j, m2) };
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        /// Can a property read the persistent record with `birds_eye`?
        property!{
            learn_cause(c: ChanId, i: nat, m: M) {
                have was_sent >= set { (c, i, m) };
                require(Inv::needs_cause(c, m));
                birds_eye let ws = pre.was_sent;
                assert(exists|d: ChanId, j: nat, m2: M|
                    ws.contains((d, j, m2)) && Inv::caused_ok(c, m, d, m2));
            }
        }

        #[inductive(boot)]
        fn boot_inductive(post: Self, chans: Set<ChanId>) { }

        #[inductive(do_send)]
        fn do_send_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, m: M) {
            assert forall|k: ChanId, i: nat, mm: M|
                (#[trigger] post.was_sent.contains((k, i, mm))) && Inv::needs_cause(k, mm)
                implies exists|d: ChanId, j: nat, m2: M|
                    post.was_sent.contains((d, j, m2)) && Inv::caused_ok(k, mm, d, m2) by {
                assert(pre.was_sent.contains((k, i, mm)));
                let (d, j, m2) = choose|d: ChanId, j: nat, m2: M|
                    pre.was_sent.contains((d, j, m2)) && Inv::caused_ok(k, mm, d, m2);
                assert(post.was_sent.contains((d, j, m2)));
            }
        }

        #[inductive(do_send_caused)]
        fn do_send_caused_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, m: M,
                                    d: ChanId, j: nat, m2: M) {
            assert forall|k: ChanId, i: nat, mm: M|
                (#[trigger] post.was_sent.contains((k, i, mm))) && Inv::needs_cause(k, mm)
                implies exists|d2: ChanId, j2: nat, m3: M|
                    post.was_sent.contains((d2, j2, m3)) && Inv::caused_ok(k, mm, d2, m3) by {
                if (k, i, mm) == (c, s.len(), m) {
                    assert(post.was_sent.contains((d, j, m2)) && Inv::caused_ok(k, mm, d, m2));
                } else {
                    assert(pre.was_sent.contains((k, i, mm)));
                    let (d2, j2, m3) = choose|d2: ChanId, j2: nat, m3: M|
                        pre.was_sent.contains((d2, j2, m3)) && Inv::caused_ok(k, mm, d2, m3);
                    assert(post.was_sent.contains((d2, j2, m3)));
                }
            }
        }
    }
}
fn main(){}

verus!{
// The lease-lock chain: an acknowledgement must be caused by a write request,
// and a write request by an acquire response. This is the cross-channel
// property that a gate alone cannot state.
pub uninterp spec fn acq_chan() -> ChanId;
pub uninterp spec fn wr_chan() -> ChanId;
pub uninterp spec fn ack_chan() -> ChanId;

#[derive(Structural, PartialEq, Eq)]
pub enum LMsg {
    Issued(u64),            // the lock server issued token t
    WriteReq(u64, u64),     // a client asks to write under (token, seq)
    Ack(u64, u64),          // storage accepted (token, seq)
}

pub struct LeaseProv;

impl Prov<LMsg> for LeaseProv {
    /// The fencing check, as before: local to the acknowledgement channel.
    open spec fn gate(c: ChanId, s: Seq<LMsg>, m: LMsg) -> bool { true }

    /// Requests and acknowledgements must point at what justified them; token
    /// issuance is the root of the chain and needs nothing.
    open spec fn needs_cause(c: ChanId, m: LMsg) -> bool {
        c == wr_chan() || c == ack_chan()
    }

    /// A write request is justified by the issuance of its token; an
    /// acknowledgement by the request it answers.
    open spec fn caused_ok(c: ChanId, m: LMsg, d: ChanId, m2: LMsg) -> bool {
        &&& c == wr_chan() ==> d == acq_chan() && m is WriteReq && m2 is Issued
                               && m->WriteReq_0 == m2->Issued_0
        &&& c == ack_chan() ==> d == wr_chan() && m is Ack && m2 is WriteReq
                                && m->Ack_0 == m2->WriteReq_0
                                && m->Ack_1 == m2->WriteReq_1
    }
}

/// The property the chain buys, read off the machine's invariant: every
/// acknowledgement in the record answers a write request that was really made.
/// A storage node cannot acknowledge a write nobody asked for.
pub proof fn lemma_ack_answers_a_request(s: ProvSM::State<LMsg, LeaseProv>, i: nat, t: u64, q: u64)
    requires
        s.provenance(),
        s.was_sent.contains((ack_chan(), i, LMsg::Ack(t, q))),
        ack_chan() != wr_chan(),
    ensures
        exists|j: nat| s.was_sent.contains((wr_chan(), j, LMsg::WriteReq(t, q))),
{
    assert(LeaseProv::needs_cause(ack_chan(), LMsg::Ack(t, q)));
    let (d, j, m2) = choose|d: ChanId, j: nat, m2: LMsg|
        s.was_sent.contains((d, j, m2)) && LeaseProv::caused_ok(ack_chan(), LMsg::Ack(t, q), d, m2);
    assert(d == wr_chan());
    assert(m2 == LMsg::WriteReq(t, q));
}
}

verus!{
/// Can a CALLER use what `learn_cause` concludes? The bound `ws` is not
/// nameable outside the property, so this is the real test.
pub proof fn try_consume<M, Inv: Prov<M>>(
    tracked inst: &ProvSM::Instance<M, Inv>,
    tracked w: &ProvSM::was_sent<M, Inv>,
    c: ChanId, i: nat, m: M,
)
    requires
        w.instance_id() == inst.id(),
        w.element() == (c, i, m),
        Inv::needs_cause(c, m),
{
    inst.learn_cause(c, i, m, w);
    assert(exists|d: ChanId, m2: M| Inv::caused_ok(c, m, d, m2));
}
}
