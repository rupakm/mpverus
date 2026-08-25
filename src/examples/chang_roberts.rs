// Chang-Roberts leader election on a ring.
//
// Node i receives on link (i-1) and sends on link i. On receiving value v:
//   v > id(i)  -> forward
//   v == id(i) -> declare self leader
//   v < id(i)  -> drop
// The safety property proved here is that only the node with the largest
// identifier can declare itself leader.
//
// The ring arithmetic below is about ids and modular arithmetic, not about the
// verification framework, and is independent of everything else in this crate.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::tokens::{InstanceId, KeyValueToken, ElementToken};
use crate::tok::*;
use crate::proc::*;

verus! {

// ---------------------------------------------------------------------------
// Ring configuration. Protocol parameters, not soundness assumptions: this just
// says "there is a ring of n >= 1 nodes with pairwise distinct ids".
// ---------------------------------------------------------------------------

pub uninterp spec fn n_nodes() -> int;
pub uninterp spec fn id(i: int) -> int;

/// Ring configuration. What remains is about IDENTITIES, not channels: channel
/// distinctness is now structural (see `chan` in `tok.rs`).
#[verifier::external_body]
pub proof fn ring_config()
    ensures
        n_nodes() >= 1,
        forall|a: int, b: int|
            0 <= a < n_nodes() && 0 <= b < n_nodes() && id(a) == id(b) ==> a == b,
{
}

/// Channel carrying messages from node j to node (j+1) mod n.
pub open spec fn link(j: int) -> ChanId { chan(0, seq![j]) }

/// Election message. `origin` and `hops` are ghost: they exist only in the
/// proof, and are erased from the running program.
pub struct Elect {
    pub val: u64,
    pub origin: Ghost<int>,
    pub hops: Ghost<nat>,
}

// ---------------------------------------------------------------------------
// The yield invariant
// ---------------------------------------------------------------------------

/// A message sitting on link `j` carries its origin's id, has travelled `hops`
/// steps around the ring from that origin, and dominates every node it has
/// passed through.
pub open spec fn msg_ok(j: int, m: Elect) -> bool {
    &&& 0 <= m.origin@ < n_nodes()
    &&& m.val as int == id(m.origin@)
    &&& j == (m.origin@ + m.hops@) % n_nodes()
    &&& forall|k: int| 0 <= k <= m.hops@ ==> m.val as int >= id(#[trigger] ((m.origin@ + k) % n_nodes()))
}

// ---------------------------------------------------------------------------
// Ring arithmetic
// ---------------------------------------------------------------------------

/// Stepping the link index forward by one matches incrementing the hop count.
pub proof fn lemma_hop_advances(o: int, h: int, i: int)
    requires
        n_nodes() >= 1,
        0 <= i < n_nodes(),
        (i - 1 + n_nodes()) % n_nodes() == (o + h) % n_nodes(),
    ensures
        (o + h + 1) % n_nodes() == i,
{
    let n = n_nodes();
    lemma_add_mod_noop(o + h, 1, n);
    assert(((o + h) % n + (1int) % n) % n == (o + h + 1) % n);
    lemma_add_mod_noop(i - 1 + n, 1, n);
    assert(((i - 1 + n) % n + (1int) % n) % n == (i - 1 + n + 1) % n);
    assert(i - 1 + n + 1 == i + n);
    lemma_mod_add_multiples_vanish(i, n);
    lemma_small_mod(i as nat, n as nat);
}

/// A message that has returned to its origin has gone all the way round.
pub proof fn lemma_full_circle(i: int, h: int)
    requires
        n_nodes() >= 1,
        0 <= i < n_nodes(),
        0 <= h,
        (i - 1 + n_nodes()) % n_nodes() == (i + h) % n_nodes(),
    ensures
        h >= n_nodes() - 1,
{
    let n = n_nodes();
    lemma_mod_equivalence(i + h, i - 1 + n, n);
    assert(i + h - (i - 1 + n) == h + 1 - n);
    assert((h + 1 - n) % n == 0);
    lemma_mod_add_multiples_vanish(h + 1 - n, n);
    assert((h + 1) % n == 0);
    lemma_mod_is_zero((h + 1) as nat, n as nat);
}

/// Every node lies on a full lap of the ring.
pub proof fn lemma_covers(i: int, h: int, p: int)
    requires
        n_nodes() >= 1,
        0 <= i < n_nodes(),
        0 <= p < n_nodes(),
        h >= n_nodes() - 1,
    ensures
        exists|k: int| 0 <= k <= h && #[trigger] ((i + k) % n_nodes()) == p,
{
    let n = n_nodes();
    let k = (p - i + n) % n;
    lemma_mod_bound(p - i + n, n);
    lemma_add_mod_noop(i, p - i + n, n);
    assert((i % n + (p - i + n) % n) % n == (i + (p - i + n)) % n);
    lemma_small_mod(i as nat, n as nat);
    assert(i + (p - i + n) == p + n);
    lemma_mod_add_multiples_vanish(p, n);
    lemma_small_mod(p as nat, n as nat);
    assert(0 <= k <= h && (i + k) % n == p);
}

} // verus!

verus!{
/// The protocol. Everything it says about its messages is these four
/// definitions and four proofs; there is no state machine to write.
pub struct CrTok;

impl NetInv<Elect> for CrTok {
    open spec fn gate(c: ChanId, s: Seq<Elect>, m: Elect) -> bool {
        forall|j: int| 0 <= j < n_nodes() && c == #[trigger] link(j) ==> msg_ok(j, m)
    }

    open spec fn wit_inv(c: ChanId, m: Elect) -> bool {
        forall|j: int| 0 <= j < n_nodes() && c == #[trigger] link(j) ==> msg_ok(j, m)
    }

    open spec fn deliverable_at(v: Seq<Elect>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn history_inv(sent: Map<ChanId, Seq<Elect>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn pair_gives(c: ChanId, m1: Elect, m2: Elect) -> bool { true }
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<Elect>>, c: ChanId,
                                i: nat, j: nat, m1: Elect, m2: Elect) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Elect>, m: Elect) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Elect) -> bool { false }
    proof fn lemma_cause_gives(c: ChanId, m: Elect, causes: Set<(ChanId, nat, Elect)>) { }
    // No cross-channel property to state over the record.
    open spec fn record_inv(was_sent: Set<(ChanId, nat, Elect)>) -> bool { true }
    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, Elect)>,
                                     c: ChanId, i: nat, m: Elect,
                                     causes: Set<(ChanId, nat, Elect)>) { }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<Elect>>, c: ChanId) { }
    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<Elect>>,
                                   was_sent: Set<(ChanId, nat, Elect)>,
                                   c: ChanId, s: Seq<Elect>, m: Elect,
                                   causes: Set<(ChanId, nat, Elect)>) { }
}
}

verus!{
pub struct StepOut {
    pub leader: bool,
    pub got: Ghost<Elect>,
    pub put: Ghost<Elect>,
}

/// One node of the ring. It owns the link it sends on and the link its
/// predecessor sends on, and nothing else; its proof never mentions another
/// node's code.
pub struct Node {
    pub i: usize,
    pub inp: In<Elect, CrTok>,
    pub out: Out<Elect, CrTok>,
    pub myid: u64,
    pub leader: bool,
}

impl Node {
    pub open spec fn inv(&self) -> bool {
        &&& self.inp.wf() && self.out.wf()
        &&& 0 <= self.i < n_nodes()
        &&& self.inp.id() == link((self.i - 1 + n_nodes()) % n_nodes())
        &&& self.out.id() == link(self.i as int)
        &&& self.myid as int == id(self.i as int)
    }

    /// One node's whole atomic action: `R . N . L*` -- a blocking receive,
    /// local comparison, and at most one send. ONE interference point, at the
    /// receive.
    pub fn cr_step(&mut self) -> (r: StepOut)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).myid == old(self).myid,
            // SAFETY: only the maximum id can ever declare itself leader.
            r.leader ==> forall|p: int|
                0 <= p < n_nodes() ==> old(self).myid as int >= id(p),
    {
        proof { ring_config(); }
        let ghost n = n_nodes();
        let i = self.i;
        let myid = self.myid;
        let ghost pred = (i - 1 + n_nodes()) % n_nodes();

        // Interference point.
        let (m, Tracked(w)) = self.inp.recv_wit();

        proof {
            lemma_mod_bound(i - 1 + n, n);
            assert(link(pred) == self.inp.id());
            assert(msg_ok(pred, m));
        }

        if m.val > myid {
            let fwd = Elect {
                val: m.val,
                origin: Ghost(m.origin@),
                hops: Ghost((m.hops@ + 1) as nat),
            };
            proof {
                lemma_hop_advances(m.origin@, m.hops@ as int, i as int);
                assert(msg_ok(i as int, fwd)) by {
                    assert forall|k: int| 0 <= k <= fwd.hops@
                        implies fwd.val as int >= id(#[trigger] ((fwd.origin@ + k) % n)) by {
                        if k <= m.hops@ { } else { assert(k == m.hops@ + 1); }
                    }
                }
                // Gate, discharged here: link(i) is the only ring link this is,
                // and the forwarded message is well formed for it.
                assert forall|j: int| 0 <= j < n_nodes() && self.out.id() == #[trigger] link(j)
                    implies msg_ok(j, fwd) by {
                    lemma_chan_inj1(0, j, i as int);
                }
            }
            self.out.send(fwd);
            StepOut { leader: false, got: Ghost(m), put: Ghost(fwd) }
        } else if m.val == myid {
            proof {
                // ids are distinct, so the message came from this very node
                assert(m.origin@ == i as int);
                lemma_full_circle(i as int, m.hops@ as int);
                assert forall|p: int| 0 <= p < n implies myid as int >= id(p) by {
                    lemma_covers(i as int, m.hops@ as int, p);
                    let k = choose|k: int| 0 <= k <= m.hops@ && #[trigger] ((i + k) % n) == p;
                }
            }
            StepOut { leader: true, got: Ghost(m), put: Ghost(m) }
        } else {
            StepOut { leader: false, got: Ghost(m), put: Ghost(m) }
        }
    }
}

impl Process for Node {
    open spec fn wf(&self) -> bool { self.inv() }

    fn step(&mut self) {
        let r = self.cr_step();
        if r.leader { self.leader = true; }
    }
}
}
