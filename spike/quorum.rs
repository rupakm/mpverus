// SPIKE, not integrated. The mathematical core of any quorum protocol,
// checked early because everything on the Paxos ladder depends on it.
//
// vstd has `lemma_len_union` and `lemma_len_intersect`, but both are
// INEQUALITIES. The disjoint-union equality that quorum intersection actually
// needs is not there, so it is proved here by induction.
use vstd::prelude::*;
use vstd::set_lib::*;
verus!{
/// Disjoint union adds. vstd gives only inequalities, so this is ours.
pub proof fn lemma_len_disjoint_union(a: Set<int>, b: Set<int>)
    requires
        a.finite(), b.finite(),
        forall|x: int| !(a.contains(x) && b.contains(x)),
    ensures
        a.union(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.is_empty() {
        assert(a.union(b) =~= b);
    } else {
        let x = a.choose();
        assert(a.contains(x));
        let a2 = a.remove(x);
        lemma_len_disjoint_union(a2, b);
        assert(a2.union(b).insert(x) =~= a.union(b));
        assert(!a2.union(b).contains(x));
    }
}

/// Two majorities of a finite set intersect. The mathematical core of Paxos.
pub proof fn lemma_quorums_intersect(u: Set<int>, a: Set<int>, b: Set<int>)
    requires
        u.finite(),
        a.subset_of(u), b.subset_of(u),
        a.len() + b.len() > u.len(),
    ensures
        exists|x: int| a.contains(x) && b.contains(x),
{
    lemma_len_subset(a, u);
    lemma_len_subset(b, u);
    assert(a.finite() && b.finite());
    if !(exists|x: int| a.contains(x) && b.contains(x)) {
        lemma_len_disjoint_union(a, b);
        assert(a.union(b).subset_of(u));
        lemma_len_subset(a.union(b), u);
    }
}
fn main(){}
}
