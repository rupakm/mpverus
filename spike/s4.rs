#![allow(unused_imports)]
use vstd::prelude::*;
verus!{
pub type ChanId = nat;
pub struct Net<M> { pub chans: Map<ChanId, Seq<M>> }

/// What a LAYER is. Abstract layers (Leslie models) implement only this.
pub trait Spec : Sized {
    type S;             // state -- arbitrary, so Leslie's TCommitState qualifies
    type A;             // actions
    type M;             // messages
    spec fn inv(s: Self::S) -> bool;
    spec fn gate(a: Self::A, req: Self::M, s: Self::S) -> bool;
    spec fn step(a: Self::A, req: Self::M, resp: Self::M, s0: Self::S, s1: Self::S) -> bool;
}

/// The BOTTOM layer: a Spec whose state is the network, plus the pool obligations.
pub trait Protocol : Spec<S = Net<<Self as Spec>::M>> {
    spec fn footprint(a: Self::A, req: Self::M) -> Set<ChanId>;
    proof fn lemma_frame(a: Self::A, req: Self::M, resp: Self::M,
                         n0: Net<Self::M>, n1: Net<Self::M>)
        requires Self::gate(a, req, n0), Self::step(a, req, resp, n0, n1)
        ensures  n0.chans.dom().subset_of(n1.chans.dom());
}

/// Refinement needs only Spec, and the two layers may differ in EVERYTHING.
pub trait Refines<Lo: Spec, Hi: Spec> : Sized {
    spec fn abs_state(s: Lo::S) -> Hi::S;
    spec fn abs_act(a: Lo::A) -> Option<Hi::A>;
    spec fn abs_msg(m: Lo::M) -> Hi::M;

    proof fn lemma_step(a: Lo::A, req: Lo::M, resp: Lo::M, s0: Lo::S, s1: Lo::S)
        requires Lo::step(a, req, resp, s0, s1)
        ensures  match Self::abs_act(a) {
            Some(h) => Hi::step(h, Self::abs_msg(req), Self::abs_msg(resp),
                                Self::abs_state(s0), Self::abs_state(s1)),
            None    => Self::abs_state(s1) == Self::abs_state(s0),   // STUTTER
        };
}

// --- a bottom layer ---
pub struct P1;
pub enum A1 { Send, Internal }
impl Spec for P1 {
    type S = Net<nat>; type A = A1; type M = nat;
    open spec fn inv(s: Net<nat>) -> bool { true }
    open spec fn gate(a: A1, req: nat, s: Net<nat>) -> bool { true }
    open spec fn step(a: A1, req: nat, resp: nat, s0: Net<nat>, s1: Net<nat>) -> bool {
        s1.chans.dom() == s0.chans.dom()
    }
}
impl Protocol for P1 {
    open spec fn footprint(a: A1, req: nat) -> Set<ChanId> { Set::empty() }
    proof fn lemma_frame(a: A1, req: nat, resp: nat, n0: Net<nat>, n1: Net<nat>) { }
}

// --- an abstract layer with a COMPLETELY DIFFERENT state type (Leslie-shaped) ---
pub struct Abs;
pub enum RmState { Working, Committed }
pub struct TCommit { pub rm1: RmState }
pub enum AbsAct { Commit }
impl Spec for Abs {
    type S = TCommit; type A = AbsAct; type M = bool;
    open spec fn inv(s: TCommit) -> bool { true }
    open spec fn gate(a: AbsAct, req: bool, s: TCommit) -> bool { true }
    open spec fn step(a: AbsAct, req: bool, resp: bool, s0: TCommit, s1: TCommit) -> bool {
        s1.rm1 is Committed
    }
}

pub struct R;
impl Refines<P1, Abs> for R {
    open spec fn abs_state(s: Net<nat>) -> TCommit { TCommit { rm1: RmState::Committed } }
    /// `Internal` refines SKIP -- impossible in the current design.
    open spec fn abs_act(a: A1) -> Option<AbsAct> {
        match a { A1::Send => Some(AbsAct::Commit), A1::Internal => None }
    }
    open spec fn abs_msg(m: nat) -> bool { true }
    proof fn lemma_step(a: A1, req: nat, resp: nat, s0: Net<nat>, s1: Net<nat>) {
        match a {
            A1::Send => { }
            A1::Internal => { assert(Self::abs_state(s1) == Self::abs_state(s0)); }
        }
    }
}
}
fn main(){}
