#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::tokens::SetToken;
use verus_state_machines_macros::tokenized_state_machine;

verus!{ pub type ChanId = nat; }

tokenized_state_machine!{
    OwnSM {
        fields {
            #[sharding(set)]
            pub recv_owned: Set<ChanId>,
        }
        transition!{
            consume(c: ChanId) { have recv_owned >= set { c }; }
        }
    }
}

verus!{
/// `split_token` and `merge_token`, currently two AXIOMS, as PROVED operations.
proof fn split_merge(
    tracked all: SetToken<ChanId, OwnSM::recv_owned>,
    c: ChanId,
)
    requires all.set().contains(c)
{
    let ghost inst = all.instance_id();
    let ghost s0 = all.set();

    // ---- fork: give channel `c` to a child, keep the rest ----
    let tracked mut parent = all;
    let tracked mut child  = SetToken::empty(inst);
    let tracked tok = parent.remove(c);
    child.insert(tok);
    assert(parent.set() == s0.remove(c));
    assert(child.set() == Set::<ChanId>::empty().insert(c));
    // disjointness is structural: `c` is gone from the parent
    assert(!parent.set().contains(c));

    // ---- join: recombine ----
    let tracked tok2 = child.remove(c);
    parent.insert(tok2);
    assert(parent.set() =~= s0);
}
}
fn main(){}
