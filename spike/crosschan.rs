#![allow(unused_imports)]
// SPIKE. Two ways to state a CROSS-CHANNEL invariant, on a miniature protocol
// with the same shape as the Paxos clause that would not go through.
//
// The protocol: an `Ack(v)` on `ack(k)` must point at a `Req(v)` on `req(k)`.
// The invariant wanted: every Ack ever sent has a matching Req.
//
// PATTERN A states it over `sent` -- a map of sequences, which is what `history_inv`
// takes today. PATTERN B states it over `was_sent` -- a set that only grows.
use vstd::prelude::*;
use vstd::tokens::{InstanceId, ElementToken};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub type Chan = nat;
pub open spec fn req(k: nat) -> Chan { 2 * k }
pub open spec fn ack(k: nat) -> Chan { 2 * k + 1 }

#[derive(Structural, PartialEq, Eq)]
pub enum M { Req(u64), Ack(u64) }

pub open spec fn is_ack_chan(c: Chan) -> bool { c % 2 == 1 }
pub open spec fn peer(c: Chan) -> Chan { (c - 1) as nat }

/// PATTERN A, the content pushed into a predicate over the two SEQUENCES.
/// The map-level statement is then a thin quantifier whose instances transfer
/// by argument equality when the map changes elsewhere.
pub open spec fn answers(acks: Seq<M>, reqs: Seq<M>) -> bool {
    forall|i: int| 0 <= i < acks.len()
        ==> exists|j: int| 0 <= j < reqs.len()
            && reqs[j] == M::Req((#[trigger] acks[i])->Ack_0)
}

/// Growing the request side keeps every answer.
pub proof fn lemma_answers_more_reqs(acks: Seq<M>, reqs: Seq<M>, m: M)
    requires answers(acks, reqs),
    ensures  answers(acks, reqs.push(m)),
{
    assert forall|i: int| 0 <= i < acks.len()
        implies exists|j: int| 0 <= j < reqs.push(m).len()
            && reqs.push(m)[j] == M::Req((#[trigger] acks[i])->Ack_0) by {
        let j0 = choose|j: int| 0 <= j < reqs.len() && reqs[j] == M::Req(acks[i]->Ack_0);
        assert(reqs.push(m)[j0] == reqs[j0]);
    }
}

/// Growing the ack side needs a justification for the new one.
pub proof fn lemma_answers_more_acks(acks: Seq<M>, reqs: Seq<M>, m: M, j0: int)
    requires
        answers(acks, reqs),
        0 <= j0 < reqs.len(),
        reqs[j0] == M::Req(m->Ack_0),
    ensures
        answers(acks.push(m), reqs),
{
    assert forall|i: int| 0 <= i < acks.push(m).len()
        implies exists|j: int| 0 <= j < reqs.len()
            && reqs[j] == M::Req((#[trigger] acks.push(m)[i])->Ack_0) by {
        if i < acks.len() {
            assert(acks.push(m)[i] == acks[i]);
            let jj = choose|j: int| 0 <= j < reqs.len() && reqs[j] == M::Req(acks[i]->Ack_0);
            assert(reqs[jj] == M::Req(acks.push(m)[i]->Ack_0));
        } else {
            assert(acks.push(m)[i] == m);
            assert(reqs[j0] == M::Req(acks.push(m)[i]->Ack_0));
        }
    }
}

/// PATTERN B, stated over the monotone record instead. Preservation is then
/// only ever about the ONE element just added.
pub open spec fn answered(ws: Set<(Chan, nat, M)>) -> bool {
    forall|c: Chan, i: nat, m: M|
        (#[trigger] ws.contains((c, i, m))) && is_ack_chan(c)
            ==> exists|j: nat| ws.contains((peer(c), j, M::Req(m->Ack_0)))
}

pub proof fn lemma_answered_grows(ws: Set<(Chan, nat, M)>, e: (Chan, nat, M), j0: nat)
    requires
        answered(ws),
        is_ack_chan(e.0) ==> ws.contains((peer(e.0), j0, M::Req(e.2->Ack_0))),
    ensures
        answered(ws.insert(e)),
{
    assert forall|c: Chan, i: nat, m: M|
        (#[trigger] ws.insert(e).contains((c, i, m))) && is_ack_chan(c)
        implies exists|j: nat| ws.insert(e).contains((peer(c), j, M::Req(m->Ack_0))) by {
        if (c, i, m) == e {
            assert(ws.insert(e).contains((peer(c), j0, M::Req(m->Ack_0))));
        } else {
            let jj = choose|j: nat| ws.contains((peer(c), j, M::Req(m->Ack_0)));
            assert(ws.insert(e).contains((peer(c), jj, M::Req(m->Ack_0))));
        }
    }
}
}


tokenized_state_machine!{
    Mini {
        fields {
            #[sharding(map)]            pub sent: Map<Chan, Seq<M>>,
            #[sharding(persistent_set)] pub was_sent: Set<(Chan, nat, M)>,
        }

        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|c: Chan, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> self.sent.dom().contains(c) && i < self.sent[c].len()
                    && self.sent[c][i as int] == m
        }

        /// PATTERN A: over the map of sequences.
        #[invariant]
        pub spec fn inv_a(&self) -> bool {
            forall|k: nat|
                self.sent.dom().contains(#[trigger] ack(k)) && self.sent.dom().contains(req(k))
                    ==> answers(self.sent[ack(k)], self.sent[req(k)])
        }

        /// PATTERN B: over the monotone record.
        #[invariant]
        pub spec fn inv_b(&self) -> bool { answered(self.was_sent) }

        init!{ boot(chans: Set<Chan>) {
            init sent = Map::new(chans, |c: Chan| Seq::<M>::empty());
            init was_sent = Set::empty();
        } }

        // Requests need no justification. Splitting the two sends is what
        // keeps the machine non-vacuous: `was_sent` starts empty and these are
        // the only sending transitions, so demanding a cause on the request
        // side too would leave no send enabled from the initial state and every
        // invariant below would hold for want of any reachable state.
        // (`have` cannot be written inside a conditional, so this is two
        // transitions rather than one with a guard.)
        transition!{
            do_send_req(c: Chan, s: Seq<M>, m: M) {
                remove sent -= [c => s];
                require(!is_ack_chan(c));
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        transition!{
            do_send_ack(c: Chan, s: Seq<M>, m: M, jj: nat) {
                remove sent -= [c => s];
                require(is_ack_chan(c) && m is Ack);
                // The justification, exactly as `send_general` demands it.
                have   was_sent >= set { (peer(c), jj, M::Req(m->Ack_0)) };
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        #[inductive(boot)]
        fn boot_inductive(post: Self, chans: Set<Chan>) {
            assert forall|k: nat|
                post.sent.dom().contains(#[trigger] ack(k)) && post.sent.dom().contains(req(k))
                implies answers(post.sent[ack(k)], post.sent[req(k)]) by {
                assert(post.sent[ack(k)] =~= Seq::<M>::empty());
            }
        }

        #[inductive(do_send_req)]
        fn do_send_req_inductive(pre: Self, post: Self, c: Chan, s: Seq<M>, m: M) {
            assert(post.sent =~= pre.sent.insert(c, s.push(m)));

            // ---- PATTERN B: the added element is not on an ack channel, so
            // the justification is not owed.
            lemma_answered_grows(pre.was_sent, (c, s.len(), m), 0);

            // ---- PATTERN A: the same fact over the map.
            assert forall|k: nat|
                post.sent.dom().contains(#[trigger] ack(k)) && post.sent.dom().contains(req(k))
                implies answers(post.sent[ack(k)], post.sent[req(k)]) by {
                assert(pre.sent.dom().contains(ack(k)) && pre.sent.dom().contains(req(k)));
                assert(is_ack_chan(ack(k))) by { assert((2 * k + 1) % 2 == 1) by (nonlinear_arith); }
                if c == req(k) {
                    assert(post.sent[ack(k)] == pre.sent[ack(k)]);
                    lemma_answers_more_reqs(pre.sent[ack(k)], s, m);
                    assert(post.sent[req(k)] == s.push(m));
                } else {
                    assert(post.sent[ack(k)] == pre.sent[ack(k)]);
                    assert(post.sent[req(k)] == pre.sent[req(k)]);
                }
            }
        }

        #[inductive(do_send_ack)]
        fn do_send_ack_inductive(pre: Self, post: Self, c: Chan, s: Seq<M>, m: M, jj: nat) {
            assert(post.sent =~= pre.sent.insert(c, s.push(m)));

            // ---- PATTERN B: one element added to a set that only grows.
            lemma_answered_grows(pre.was_sent, (c, s.len(), m), jj);

            // ---- PATTERN A: the same fact over the map.
            assert forall|k: nat|
                post.sent.dom().contains(#[trigger] ack(k)) && post.sent.dom().contains(req(k))
                implies answers(post.sent[ack(k)], post.sent[req(k)]) by {
                assert(pre.sent.dom().contains(ack(k)) && pre.sent.dom().contains(req(k)));
                assert(!is_ack_chan(req(k))) by { assert((2 * k) % 2 == 0) by (nonlinear_arith); }
                if c == ack(k) {
                    assert(post.sent[req(k)] == pre.sent[req(k)]);
                    assert(pre.sent[ack(k)] == s);
                    assert(pre.sent[peer(c)][jj as int] == M::Req(m->Ack_0));
                    assert(peer(c) == req(k));
                    lemma_answers_more_acks(s, pre.sent[req(k)], m, jj as int);
                    assert(post.sent[ack(k)] == s.push(m));
                } else {
                    assert(post.sent[ack(k)] == pre.sent[ack(k)]);
                    assert(post.sent[req(k)] == pre.sent[req(k)]);
                }
            }
        }
    }
}
verus!{
/// NON-VACUITY. A request send is enabled from the initial state.
///
/// This is what the split buys. When `do_send` demanded a cause on EVERY
/// channel, its guard could never be met: `boot` starts `was_sent` empty and
/// sending was the only way to add to it, so no state past `boot` was
/// reachable and both invariants above held for want of anything to check.
pub proof fn lemma_req_send_enabled(k: nat)
    ensures
        // the guard of `do_send_req`, at a request channel
        !is_ack_chan(req(k)),
        // ... and the guard of `do_send_ack` is the one that needs a cause
        is_ack_chan(ack(k)),
{
    assert((2 * k) % 2 == 0) by (nonlinear_arith);
    assert((2 * k + 1) % 2 == 1) by (nonlinear_arith);
}

fn main(){} }
