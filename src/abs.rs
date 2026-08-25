// EXPERIMENT, on a branch, to be kept or discarded on evidence.
//
// Phase 3, tier T1: connect running code to an abstract model by attributing
// abstract actions to the machine's TRANSITIONS rather than to function bodies.
// See docs/plan.md, Phase 3.
//
// Nothing here changes any existing type. `NetAbs` is a separate trait, so a
// protocol that does not implement it costs nothing and discarding the whole
// idea is one file deletion.
use vstd::prelude::*;
use crate::tok::*;

verus!{

/// A refinement mapping from the network machine to an abstract model.
///
/// The mapping reads `sent`, not the whole machine state. Two reasons, and both
/// are what make it stable without an atomicity argument: `sent` only ever
/// grows at one key per transition, so another thread cannot invalidate a fact
/// derived from it; and `do_recv` and `alloc` do not touch it, so they are
/// stuttering steps for free, with no obligation to discharge.
///
/// (`was_sent` would serve equally for stability, but `sent` carries per-channel
/// ORDER natively, and every abstract state tried so far has wanted order.)
pub trait NetAbs<M, Inv: NetInv<M>> : Sized {
    /// The model's state.
    type S;
    /// The model's actions.
    type A;

    /// The refinement mapping.
    spec fn abs(sent: Map<ChanId, Seq<M>>) -> Self::S;

    /// Which abstract action this send realises; `None` is a stuttering step.
    ///
    /// `sent` is available because attribution may have to depend on history --
    /// the send that completes a quorum is the one that acts, and nothing about
    /// that message says so. A protocol that can decide by message shape alone
    /// should ignore it, and how often that is possible is the open question
    /// about this design.
    spec fn act_of(sent: Map<ChanId, Seq<M>>, c: ChanId, m: M) -> Option<Self::A>;

    /// The model's own gate and transition relation.
    spec fn hi_gate(a: Self::A, s: Self::S) -> bool;
    spec fn hi_step(a: Self::A, s: Self::S, s2: Self::S) -> bool;

    /// THE obligation, one per protocol.
    ///
    /// Its arguments and hypotheses are exactly `do_send`'s, which is the point:
    /// `do_send` is the only transition that changes `sent`, so discharging this
    /// says every step of the machine is a step of the model or invisible to it.
    proof fn lemma_send_refines(
        sent: Map<ChanId, Seq<M>>,
        was_sent: Set<(ChanId, nat, M)>,
        c: ChanId, s: Seq<M>, m: M,
        causes: Set<(ChanId, nat, M)>,
    )
        requires
            sent.dom().contains(c), sent[c] == s,
            Inv::gate(c, s, m),
            Inv::record_inv(was_sent),
            causes.subset_of(was_sent),
            Inv::needs_cause(c, m) ==> Inv::caused_by(c, m, causes),
        ensures
            ({
                let post = sent.insert(c, s.push(m));
                match Self::act_of(sent, c, m) {
                    Some(a) => Self::hi_gate(a, Self::abs(sent))
                            && Self::hi_step(a, Self::abs(sent), Self::abs(post)),
                    None => Self::abs(post) == Self::abs(sent),
                }
            });
}

} // verus!
