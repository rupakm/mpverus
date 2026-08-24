#![allow(unused_imports)]
// SPIKE, not integrated. Can a service CONSUME `history_inv` -- a guarantee about
// pairs of messages -- on a channel it does not own?
//
// Today `history_inv` is write-only: it is proved as a machine invariant and there is
// no property that reads it back. A protocol whose guarantee is pairwise
// (heartbeat: sequence numbers increase) can state it and cannot use it.
use vstd::prelude::*;
use vstd::tokens::{InstanceId, ElementToken};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub type ChanId = nat;

pub trait Pair<M> : Sized {
    spec fn gate(c: ChanId, s: Seq<M>, m: M) -> bool;
    /// The pairwise guarantee, over the send histories.
    spec fn history_inv(sent: Map<ChanId, Seq<M>>) -> bool;
    /// What a reader may conclude about TWO messages it holds witnesses for.
    /// Pure in (c, m1, m2), for the same reason `cause_gives` must be pure:
    /// anything mentioning the histories is projected away.
    spec fn pair_gives(c: ChanId, m1: M, m2: M) -> bool;

    proof fn lemma_history_inv_init(chans: Set<ChanId>)
        ensures Self::history_inv(Map::new(chans, |c: ChanId| Seq::<M>::empty()));

    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<M>>, c: ChanId, s: Seq<M>, m: M)
        requires
            Self::history_inv(sent), Self::gate(c, s, m),
            sent.dom().contains(c), sent[c] == s,
        ensures
            Self::history_inv(sent.insert(c, s.push(m)));

    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<M>>, c: ChanId,
                                i: nat, j: nat, m1: M, m2: M)
        requires
            Self::history_inv(sent),
            sent.dom().contains(c),
            i < j < sent[c].len(),
            sent[c][i as int] == m1,
            sent[c][j as int] == m2,
        ensures
            Self::pair_gives(c, m1, m2);
}
}

tokenized_state_machine!{
    PairSM<M, Inv: Pair<M>> {
        fields {
            #[sharding(map)]            pub sent: Map<ChanId, Seq<M>>,
            #[sharding(persistent_set)] pub was_sent: Set<(ChanId, nat, M)>,
            #[sharding(constant)]       pub inv: PhantomData<Inv>,
        }

        /// A witness names a real position in the history it came from.
        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|c: ChanId, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> self.sent.dom().contains(c) && i < self.sent[c].len()
                    && self.sent[c][i as int] == m
        }

        #[invariant]
        pub spec fn protocol_history_inv(&self) -> bool { Inv::history_inv(self.sent) }

        init!{ boot(chans: Set<ChanId>) {
            init sent = Map::new(chans, |c: ChanId| Seq::<M>::empty());
            init was_sent = Set::empty();
            init inv = PhantomData;
        } }

        transition!{ do_send(c: ChanId, s: Seq<M>, m: M) {
            remove sent -= [c => s];
            require(Inv::gate(c, s, m));
            add    sent += [c => s.push(m)];
            add    was_sent (union)= set { (c, s.len(), m) };
        } }

        /// THE POINT OF THE SPIKE. Two witnesses in, a pure fact about the two
        /// messages out. The reader owns neither the channel nor the history.
        property!{
            learn_pair(c: ChanId, i: nat, j: nat, m1: M, m2: M) {
                have was_sent >= set { (c, i, m1) };
                have was_sent >= set { (c, j, m2) };
                require(i < j);
                birds_eye let s = pre.sent;
                assert(Inv::pair_gives(c, m1, m2)) by {
                    Inv::lemma_pair_gives(s, c, i, j, m1, m2);
                };
            }
        }

        #[inductive(boot)]    fn boot_inductive(post: Self, chans: Set<ChanId>) {
            Inv::lemma_history_inv_init(chans);
        }
        #[inductive(do_send)] fn send_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, m: M) {
            Inv::lemma_history_inv_preserved(pre.sent, c, s, m);
            assert(post.sent =~= pre.sent.insert(c, s.push(m)));
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                implies post.sent.dom().contains(k) && i < post.sent[k].len()
                    && post.sent[k][i as int] == mm by {
                if (k, i, mm) != (c, s.len(), m) { assert(pre.was_sent.contains((k, i, mm))); }
                if k == c { assert(post.sent[c] == s.push(m)); }
            }
        }
    }
}
verus!{
// A concrete protocol with a PAIRWISE guarantee, exactly heartbeat's shape:
// numbers on a link strictly increase. No single message can express it.
pub struct Hb;

impl Pair<u64> for Hb {
    open spec fn gate(c: ChanId, s: Seq<u64>, m: u64) -> bool {
        forall|x: int| 0 <= x < s.len() ==> #[trigger] s[x] < m
    }
    open spec fn history_inv(sent: Map<ChanId, Seq<u64>>) -> bool {
        forall|c: ChanId, x: int, y: int|
            sent.dom().contains(c) && 0 <= x < y < sent[c].len()
                ==> #[trigger] sent[c][x] < #[trigger] sent[c][y]
    }
    /// The consumable form: pure in the two messages.
    open spec fn pair_gives(c: ChanId, m1: u64, m2: u64) -> bool { m1 < m2 }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }

    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<u64>>, c: ChanId, s: Seq<u64>, m: u64) {
        let post = sent.insert(c, s.push(m));
        assert forall|k: ChanId, x: int, y: int|
            post.dom().contains(k) && 0 <= x < y < post[k].len()
            implies #[trigger] post[k][x] < #[trigger] post[k][y] by {
            if k == c {
                if y < s.len() { assert(sent[c][x] < sent[c][y]); }
                else { assert(post[c][y] == m); assert(s[x] < m); }
            } else {
                assert(post[k] == sent[k]);
                assert(sent[k][x] < sent[k][y]);
            }
        }
    }

    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<u64>>, c: ChanId,
                                i: nat, j: nat, m1: u64, m2: u64) {
        assert(sent[c][i as int] < sent[c][j as int]);
    }
}

/// THE TEST. A reader holding two witnesses for a channel it does not own
/// learns that the numbers increase -- which today it cannot.
pub proof fn watcher_learns(
    tracked inst: &PairSM::Instance<u64, Hb>,
    tracked w1: &PairSM::was_sent<u64, Hb>,
    tracked w2: &PairSM::was_sent<u64, Hb>,
    c: ChanId, i: nat, j: nat, m1: u64, m2: u64,
)
    requires
        w1.instance_id() == inst.id(), w1.element() == (c, i, m1),
        w2.instance_id() == inst.id(), w2.element() == (c, j, m2),
        i < j,
{
    inst.learn_pair(c, i, j, m1, m2, w1, w2);
    assert(m1 < m2);
}

fn main() { } }
