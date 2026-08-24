use vstd::prelude::*;
use vstd::set_lib::*;

verus!{
/// Two majorities of a finite set intersect. The mathematical core of Paxos.
///
/// Every `Set` in this vstd is finite, so there is no finiteness side condition
/// to carry; and disjoint union adding is `lemma_set_disjoint_lens`.
pub proof fn lemma_quorums_intersect(u: Set<int>, a: Set<int>, b: Set<int>)
    requires
        a.subset_of(u), b.subset_of(u),
        a.len() + b.len() > u.len(),
    ensures
        exists|x: int| a.contains(x) && b.contains(x),
{
    lemma_len_subset(a, u);
    lemma_len_subset(b, u);
    if !(exists|x: int| a.contains(x) && b.contains(x)) {
        assert(a.disjoint(b));
        lemma_set_disjoint_lens(a, b);
        assert(a.union(b) =~= a + b);
        assert(a.union(b).subset_of(u));
        lemma_len_subset(a.union(b), u);
    }
}
}
