use vstd::prelude::*;
use crate::tok::{NetInv, ChanId};

verus! {

/// WHAT A LAYER IS. A gated transition system: state, actions, messages, an
/// invariant, and Civl's (rho, tau) pair. Deliberately says NOTHING about
/// networks or channels, so that an abstract layer -- a Leslie model, say --
/// can be stated over whatever state is natural for it.
pub trait Spec : Sized {
    /// State. `Net<M>` at the bottom; arbitrary above.
    type S;
    /// Action index: one variant per atomic action of this layer.
    type A;
    /// Message type.
    type M;

    /// The invariant every thread may assume at an interference point and must
    /// preserve at each of its own steps. At the bottom layer it is stated over
    /// send histories, which only grow, so it is stable under interference
    /// without further argument.
    spec fn inv(s: Self::S) -> bool;

    /// GATE (Civl's `rho`): the states from which the action must not FAIL.
    /// Distinct from blocking, which is the absence of a `step`. Keeping the two
    /// apart is what makes layered refinement stateable.
    spec fn gate(a: Self::A, req: Self::M, s: Self::S) -> bool;

    /// The action's transition relation (Civl's `tau`).
    spec fn step(a: Self::A, req: Self::M, resp: Self::M,
                 s0: Self::S, s1: Self::S) -> bool;
}




// ---------------------------------------------------------------------------
// The bottom of a refinement stack, derived from the protocol.
//
// A stack has to start somewhere. Writing the bottom layer out by hand means
// restating the protocol's gate as `gate` and its transition as `step`, which
// proves refinement about a copy of the protocol rather than about the protocol
// itself, with nothing requiring the copy to agree.
//
// `Layered` instead has a protocol name its machine's own state, invariant and
// transition relations, and `BottomLayer<T>` is those, so there is no second
// definition to keep consistent. Implementing it is optional: a protocol that
// needs no refinement stack need not.
// ---------------------------------------------------------------------------

pub trait Layered<M> : NetInv<M> {
    /// The machine's own state.
    type St;

    /// The machine's invariant, as a predicate on that state.
    spec fn st_inv(s: Self::St) -> bool;

    /// The send gate as a predicate on the machine's state.
    /// `NetInv::gate` is given a channel's history rather than the machine's
    /// state, which a state-level layer does not have; `lemma_send_gate_st`
    /// below requires the two to agree.
    spec fn st_send_gate(s: Self::St, c: ChanId, m: M) -> bool;

    /// The machine's own transition relations. A protocol supplies these by
    /// naming the generated relations, one line each, so that `step` below is
    /// the protocol's transition rather than a restatement of it.
    spec fn st_send(s0: Self::St, s1: Self::St, c: ChanId, q: Seq<M>, m: M) -> bool;
    spec fn st_recv(s0: Self::St, s1: Self::St, c: ChanId, q: Seq<M>, m: M) -> bool;

    /// Consistency condition: the state-level gate is implied by the machine's
    /// own precondition. Claiming a gate the machine does not enforce makes
    /// this fail to verify.
    proof fn lemma_send_gate_st(s0: Self::St, s1: Self::St, c: ChanId,
                                q: Seq<M>, m: M)
        requires
            Self::st_send(s0, s1, c, q, m),
        ensures
            Self::st_send_gate(s0, c, m);
}

/// The two things a channel protocol does, as an action index.
pub enum ChanAct { Send(ChanId), Recv(ChanId) }

/// The bottom of a refinement stack, derived from the protocol.
pub struct BottomLayer<T> {
    pub p: core::marker::PhantomData<T>,
}

impl<M, T: Layered<M>> Spec for BottomLayer<(M, T)> {
    type M = M;
    type A = ChanAct;
    type S = T::St;

    open spec fn inv(s: T::St) -> bool { T::st_inv(s) }

    open spec fn gate(a: ChanAct, req: M, s: T::St) -> bool {
        match a {
            ChanAct::Send(c) => T::st_send_gate(s, c, req),
            // A receive does not fail; it waits. This is the distinction
            // between a gate and blocking.
            ChanAct::Recv(c) => true,
        }
    }

    /// The removed history is existentially quantified because it is determined
    /// by `s0` -- the machine's transitions name it as a parameter.
    open spec fn step(a: ChanAct, req: M, resp: M, s0: T::St, s1: T::St) -> bool {
        match a {
            ChanAct::Send(c) => exists|q: Seq<M>| T::st_send(s0, s1, c, q, req),
            ChanAct::Recv(c) => exists|q: Seq<M>| T::st_recv(s0, s1, c, q, req),
        }
    }
}

/// `Lo` refines `Hi`, where `Hi` is the layer above (Civl Definition 3.1,
/// extended with an Abadi--Lamport refinement mapping).
///
/// Both sides are `Spec`s, not `Protocol`s, so the two layers may differ in
/// EVERYTHING: state, actions, and messages. That is what lets an abstract
/// layer be stated over whatever state is natural for it -- a set of decided
/// values, or one status per participant -- rather than being forced to talk
/// about a network.
pub trait Refines<Lo: Spec, Hi: Spec> : Sized {
    /// The refinement MAPPING: how a concrete state looks from above.
    spec fn abs_state(s: Lo::S) -> Hi::S;

    /// Which abstract action each concrete action refines. Not injective in
    /// general: a whole family of concrete actions may collapse to one abstract
    /// action, which is the point of a layer.
    ///
    /// `None` means the action refines a stuttering step: it is invisible from
    /// above. Most internal steps of an implementation are of this kind.
    /// Without it, every low-level message would have to remain visible at
    /// every layer of the stack.
    spec fn abs_act(a: Lo::A) -> Option<Hi::A>;

    /// How a concrete message looks from above.
    spec fn abs_msg(m: Lo::M) -> Hi::M;

    /// The abstract invariant is implied by the concrete one, THROUGH the
    /// mapping: raising a layer may only forget detail, never assume more.
    proof fn lemma_inv(s: Lo::S)
        requires Lo::inv(s)
        ensures  Hi::inv(Self::abs_state(s));

    /// Civl Definition 3.1 (1): the abstract action fails at least as often as
    /// the concrete one, so wherever the abstraction is safe the implementation
    /// is too. Vacuous for a stuttering action, which cannot fail.
    ///
    /// The concrete invariant is available: refinement is only ever appealed to
    /// at reachable states, so requiring it to hold at unreachable ones would
    /// reject perfectly good abstractions. An abstraction that forgets the
    /// information a gate needs must recover it from the invariant, and this is
    /// where it does so.
    proof fn lemma_gate(a: Lo::A, req: Lo::M, s: Lo::S)
        requires
            Lo::inv(s),
            Self::abs_act(a) is Some,
            Hi::gate(Self::abs_act(a)->Some_0, Self::abs_msg(req), Self::abs_state(s)),
        ensures
            Lo::gate(a, req, s);

    /// Civl Definition 3.1 (2): wherever the abstract action is safe, every
    /// concrete transition is an abstract one, or is invisible from above.
    proof fn lemma_step(a: Lo::A, req: Lo::M, resp: Lo::M, s0: Lo::S, s1: Lo::S)
        requires
            Lo::inv(s0),
            Lo::step(a, req, resp, s0, s1),
            Self::abs_act(a) is Some
                ==> Hi::gate(Self::abs_act(a)->Some_0, Self::abs_msg(req),
                             Self::abs_state(s0)),
        ensures
            match Self::abs_act(a) {
                Some(h) => Hi::step(h, Self::abs_msg(req), Self::abs_msg(resp),
                                    Self::abs_state(s0), Self::abs_state(s1)),
                // STUTTER: the concrete step is invisible from above.
                None    => Self::abs_state(s1) == Self::abs_state(s0),
            };
}

/// Transport a concrete step up one layer. This is what a `refines` annotation
/// on a yield procedure amounts to at the library level.
pub proof fn lift<Lo: Spec, Hi: Spec, R: Refines<Lo, Hi>>(
    a: Lo::A, req: Lo::M, resp: Lo::M, s0: Lo::S, s1: Lo::S,
)
    requires
        Lo::inv(s0),
        Lo::step(a, req, resp, s0, s1),
        R::abs_act(a) is Some,
        Hi::gate(R::abs_act(a)->Some_0, R::abs_msg(req), R::abs_state(s0)),
    ensures
        Hi::step(R::abs_act(a)->Some_0, R::abs_msg(req), R::abs_msg(resp),
                 R::abs_state(s0), R::abs_state(s1))
{
    R::lemma_step(a, req, resp, s0, s1);
}

/// Transport a STUTTERING step: nothing happens upstairs.
pub proof fn lift_stutter<Lo: Spec, Hi: Spec, R: Refines<Lo, Hi>>(
    a: Lo::A, req: Lo::M, resp: Lo::M, s0: Lo::S, s1: Lo::S,
)
    requires
        Lo::inv(s0),
        Lo::step(a, req, resp, s0, s1),
        R::abs_act(a) is None,
    ensures
        R::abs_state(s1) == R::abs_state(s0)
{
    R::lemma_step(a, req, resp, s0, s1);
}

/// Composing two abstraction maps. An action is invisible at the top if it is
/// invisible at either step.
pub open spec fn abs_act2<A: Spec, B: Spec, C: Spec, R1: Refines<A, B>, R2: Refines<B, C>>(
    a: A::A,
) -> Option<C::A> {
    match R1::abs_act(a) {
        None    => None,
        Some(b) => R2::abs_act(b),
    }
}

/// Refinement is transitive, so stacks of layers compose: a step justified at
/// the bottom is a step of the top layer, through any number of intermediate
/// layers, each with its own state, actions and messages, and any of which may
/// absorb the step into stuttering.
pub proof fn refines_trans<
    A: Spec,
    B: Spec,
    C: Spec,
    R1: Refines<A, B>,
    R2: Refines<B, C>,
>(a: A::A, req: A::M, resp: A::M, s0: A::S, s1: A::S)
    requires
        A::inv(s0),
        A::step(a, req, resp, s0, s1),
        R1::abs_act(a) is Some
            ==> B::gate(R1::abs_act(a)->Some_0, R1::abs_msg(req), R1::abs_state(s0)),
        abs_act2::<A, B, C, R1, R2>(a) is Some
            ==> C::gate(abs_act2::<A, B, C, R1, R2>(a)->Some_0,
                        R2::abs_msg(R1::abs_msg(req)),
                        R2::abs_state(R1::abs_state(s0))),
    ensures
        match abs_act2::<A, B, C, R1, R2>(a) {
            Some(c) => C::step(c,
                               R2::abs_msg(R1::abs_msg(req)),
                               R2::abs_msg(R1::abs_msg(resp)),
                               R2::abs_state(R1::abs_state(s0)),
                               R2::abs_state(R1::abs_state(s1))),
            None    => R2::abs_state(R1::abs_state(s1))
                    == R2::abs_state(R1::abs_state(s0)),
        },
{
    R1::lemma_inv(s0);
    R1::lemma_step(a, req, resp, s0, s1);
    match R1::abs_act(a) {
        None => {
            // Invisible already at the middle layer, hence at the top: the
            // mapping is a function of the state.
            assert(R1::abs_state(s1) == R1::abs_state(s0));
        }
        Some(b) => {
            R2::lemma_step(b, R1::abs_msg(req), R1::abs_msg(resp),
                           R1::abs_state(s0), R1::abs_state(s1));
        }
    }
}

/// Invariants weaken up a stack too, through the composed mapping.
pub proof fn inv_trans<
    A: Spec,
    B: Spec,
    C: Spec,
    R1: Refines<A, B>,
    R2: Refines<B, C>,
>(s: A::S)
    requires A::inv(s)
    ensures  C::inv(R2::abs_state(R1::abs_state(s)))
{
    R1::lemma_inv(s);
    R2::lemma_inv(R1::abs_state(s));
}

} // verus!
