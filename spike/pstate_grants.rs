#![allow(unused_imports)]
// EXPERIMENT (round 2): does protocol state in the machine buy the property
// that provenance and gates cannot reach?
//
// The target is the lease lock's GLOBAL GRANT MONOTONICITY: every token the
// server issues exceeds every token it has issued before. `src/examples/
// leaselock.rs` records why that is out of reach today -- grants travel on
// `acq_rsp(w)`, one channel per writer, and a gate sees one channel, so nothing
// relates a grant to grants sent to other writers. The server's counter is a
// local variable nobody can read.
//
// This is that protocol cut down to its bones: writers indexed by `int`,
// messages that are just tokens, and the server's counter as a machine field.
use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

tokenized_state_machine!{
    Grants {
        fields {
            /// One reply channel per writer. `acq_rsp(w)` in the real protocol.
            #[sharding(map)]            pub sent:     Map<int, Seq<u64>>,
            /// The record. Positions are per channel, exactly as in `NetSM`.
            #[sharding(persistent_set)] pub was_sent: Set<(int, nat, u64)>,
            /// THE NEW FIELD: the server's counter, owned by the server.
            #[sharding(variable)]       pub hi:       u64,
        }

        /// Every token ever issued is at most the counter. This is the clause
        /// that cannot be written at all without the field.
        #[invariant]
        pub spec fn issued_below_hi(&self) -> bool {
            forall|w: int, i: nat, t: u64|
                (#[trigger] self.was_sent.contains((w, i, t))) ==> 0 < t <= self.hi
        }

        /// The record and the histories agree, as in `NetSM`.
        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|w: int, i: int|
                self.sent.dom().contains(w) && 0 <= i < self.sent[w].len()
                    ==> self.was_sent.contains((w, i as nat, #[trigger] self.sent[w][i]))
        }

        init!{ boot(ws: Set<int>) {
            init sent     = Map::new(ws, |w: int| Seq::<u64>::empty());
            init was_sent = Set::empty();
            init hi       = 0;
        } }

        /// A grant. The send and the counter bump are ONE transition.
        ///
        /// That is the design point. With them separate -- the spiked
        /// `do_pstep` plus an ordinary `do_send` -- a server could read its
        /// counter, send twice, and bump once, and the invariant would not be
        /// inductive. The caller must hold BOTH the channel's token and the
        /// counter, which is exactly who the server is.
        transition!{ grant(w: int, s: Seq<u64>, t: u64) {
            remove sent -= [w => s];
            require(t >= 1 && t - 1 == pre.hi);
            update hi    = t;
            add    sent += [w => s.push(t)];
            add    was_sent (union)= set { (w, s.len(), t) };
        } }

        #[inductive(boot)]
        fn boot_inductive(post: Self, ws: Set<int>) {
            assert forall|w: int, i: int|
                post.sent.dom().contains(w) && 0 <= i < post.sent[w].len()
                    implies post.was_sent.contains((w, i as nat, #[trigger] post.sent[w][i])) by {
                assert(post.sent[w] =~= Seq::<u64>::empty());
            }
        }

        #[inductive(grant)]
        fn grant_inductive(pre: Self, post: Self, w: int, s: Seq<u64>, t: u64) {
            assert forall|x: int, i: nat, u: u64|
                (#[trigger] post.was_sent.contains((x, i, u))) implies 0 < u <= post.hi by {
                if (x, i, u) != (w, s.len(), t) { assert(pre.was_sent.contains((x, i, u))); }
            }
            assert forall|x: int, i: int|
                post.sent.dom().contains(x) && 0 <= i < post.sent[x].len()
                    implies post.was_sent.contains((x, i as nat, #[trigger] post.sent[x][i])) by {
                if x == w {
                    assert(post.sent[w] == s.push(t));
                    if i < s.len() { assert(pre.sent[w][i] == s[i]); }
                }
            }
        }
    }
}

verus!{

/// GLOBAL GRANT MONOTONICITY, the property this experiment exists for.
///
/// A grant issued now strictly exceeds every token issued before it, ACROSS ALL
/// WRITERS' CHANNELS. No gate can say this and no provenance edge carries it;
/// it holds because every earlier token is bounded by a counter that this step
/// raises.
pub proof fn lemma_grant_exceeds_all_earlier(
    pre: Grants::State, post: Grants::State, w: int, s: Seq<u64>, t: u64,
)
    requires
        pre.issued_below_hi(),
        t >= 1 && t - 1 == pre.hi,
        post.was_sent == pre.was_sent.insert((w, s.len(), t)),
    ensures
        forall|x: int, i: nat, u: u64|
            (#[trigger] pre.was_sent.contains((x, i, u))) ==> u < t,
{
}

/// And so no token is ever issued twice, which is what the fencing argument
/// needs: two writers cannot hold the same token.
pub proof fn lemma_grants_distinct(
    pre: Grants::State, w: int, s: Seq<u64>, t: u64,
)
    requires
        pre.issued_below_hi(),
        t >= 1 && t - 1 == pre.hi,
    ensures
        forall|x: int, i: nat| !(#[trigger] pre.was_sent.contains((x, i, t))),
{
}

/// NOT VACUOUS. The guard is satisfiable from the initial state and from any
/// state the machine can reach, so the invariants above are about a machine
/// that actually moves. `spike/crosschan.rs` was vacuous for want of this
/// check: a cause obligation that no first send could ever discharge.
pub proof fn lemma_grant_enabled(pre: Grants::State)
    requires pre.hi < u64::MAX,
    ensures
        // the guard of `grant`, at the token the server would actually pick
        ((pre.hi + 1) as u64) >= 1,
        ((pre.hi + 1) as u64) - 1 == pre.hi,
{
}

// ---------------------------------------------------------------------------
// WHAT THIS SETTLES
// ---------------------------------------------------------------------------
//
// PROVABLE, and not provable today by any other means in this development:
// global grant monotonicity, and with it that no token is ever issued twice.
// The lease lock's fencing argument wants exactly that -- two writers must not
// hold the same token -- and today it is reachable only per channel.
//
// THE PLAN'S SHAPE IS WRONG IN ONE RESPECT. `docs/plan.md` proposes `do_pstep`
// to advance a participant's own state, alongside the existing `do_send`. That
// does not suffice, and the failure is not subtle: a server could read its
// counter, send two grants, and bump once. Removing `update hi = t` from the
// transition below and weakening its guard accordingly makes
// `grant_inductive` fail, which is the check. The send and the state update
// must be ONE transition, so the caller has to hold both the channel's token
// and the counter -- which is precisely the definition of the server.
//
// THE COST OF INTEGRATING IT into `NetSM`, measured rather than guessed:
//
//   * `NetSM` gains a field, so a new `do_send_p` transition must re-establish
//     all SEVEN of its invariants. `do_send_inductive` is 40 lines today and
//     the new one would be at least that.
//   * `NetInv` gains three members -- `type P`, `pinit`, and a gate that reads
//     and writes the state -- on top of the 22 it already has.
//   * NINE protocols implement `NetInv`, and eight of them want none of this,
//     so each writes about four lines of unit-typed boilerplate. Rust has no
//     stable associated-type defaults, so there is no way to avoid it, and the
//     macro that would paper over it does not survive `verus!` (see plan.md).
//   * A new trusted primitive, and an `Out` method that carries the state
//     token alongside the channel token.
//
// So the trade is: one property that is otherwise unreachable, against a field
// on the shared machine, a fourth transition, and boilerplate in every protocol
// including the eight that do not use it.

fn main() { }
}
