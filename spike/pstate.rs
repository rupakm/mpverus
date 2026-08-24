#![allow(unused_imports)]
// SPIKE, not integrated. Feasibility check for protocol state inside the
// network machine: can a TSM field take a protocol-supplied associated type,
// and can a transition READ a map field without consuming it? Both yes.
// See docs/plan.md, "Protocol state in the network machine".
use vstd::prelude::*;
use vstd::tokens::{InstanceId, KeyValueToken, ElementToken};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;

verus!{
pub trait Proto : Sized {
    type P;                                        // protocol's own ghost state
    type F;                                        // facts exportable from it
    spec fn pinit(id: int) -> Self::P;
    spec fn pstep(id: int, old: Self::P, new: Self::P) -> bool;
    spec fn pfact_ok(id: int, p: Self::P, f: Self::F) -> bool;
}
}

tokenized_state_machine!{
    PSM<Pr: Proto> {
        fields {
            #[sharding(map)]            pub pstate: Map<int, Pr::P>,
            #[sharding(persistent_set)] pub pfacts: Set<Pr::F>,
            #[sharding(constant)]       pub ph: PhantomData<Pr>,
        }

        #[invariant]
        pub spec fn facts_sound(&self) -> bool { true }

        init!{ boot(ids: Set<int>) {
            init pstate = Map::new(ids, |i: int| Pr::pinit(i));
            init pfacts = Set::empty();
            init ph = PhantomData;
        } }

        // A participant advances its OWN state. Exclusive, so no interference.
        transition!{ do_pstep(id: int, old: Pr::P, new: Pr::P) {
            remove pstate -= [id => old];
            require(Pr::pstep(id, old, new));
            add    pstate += [id => new];
        } }

        // ... and exports a monotone fact from it.
        transition!{ publish(id: int, p: Pr::P, f: Pr::F) {
            have   pstate >= [id => p];
            require(Pr::pfact_ok(id, p, f));
            add    pfacts (union)= set { f };
        } }

        #[inductive(boot)]     fn boot_inductive(post: Self, ids: Set<int>) { }
        #[inductive(do_pstep)] fn s_inductive(pre: Self, post: Self, id: int, old: Pr::P, new: Pr::P) { }
        #[inductive(publish)]  fn p_inductive(pre: Self, post: Self, id: int, p: Pr::P, f: Pr::F) { }
    }
}
verus!{ fn main() { } }
