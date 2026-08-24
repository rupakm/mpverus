// Many producers, one consumer.
//
// Unordered delivery from several senders is modelled as a family of
// per-producer channels rather than one channel with many senders. A single
// send history with several concurrent appenders cannot be exclusively owned,
// and without exclusive ownership `send` is not a left mover.
//
// Dividing by sender retains per-producer order, which a real multi-producer
// channel also retains, and leaves delivery in any order on the receive side,
// where `recv_any` expresses it.
use vstd::prelude::*;
use vstd::tokens::{InstanceId, MapToken, KeyValueToken, ElementToken};
use crate::tok::*;
use crate::proc::*;

verus! {

/// Producer `w`'s channel into the hub.
/// Producer `w`'s channel into the hub. Concrete, so distinctness of
/// producers' channels is structural rather than assumed.
pub open spec fn hub_from(w: int) -> ChanId { chan(0, seq![w]) }
pub uninterp spec fn n_producers() -> int;

/// What counts as an acceptable item. Left abstract: the point is that the
/// property survives arbitrary interleaving of the producers.
pub uninterp spec fn good(v: u64) -> bool;

/// The only assumption: how many producers there are.
#[verifier::external_body]
pub proof fn n_producers_pos()
    ensures
        n_producers() > 0,
{
}

/// The facts call sites need. Distinctness of producers' channels is proved
/// rather than assumed.
pub proof fn hub_config()
    ensures
        n_producers() > 0,
        forall|w: int, x: int| w != x
            ==> #[trigger] hub_from(w) != #[trigger] hub_from(x),
{
    n_producers_pos();
    assert forall|w: int, x: int| w != x
        implies #[trigger] hub_from(w) != #[trigger] hub_from(x) by {
        if hub_from(w) == hub_from(x) { lemma_chan_inj1(0, w, x); }
    }
}

#[derive(Structural, PartialEq, Eq)]
pub struct Item { pub v: u64 }

pub open spec fn is_hub(c: ChanId) -> bool {
    exists|w: int| 0 <= w < n_producers() && c == #[trigger] hub_from(w)
}

} // verus!

verus!{
/// The protocol. Everything it says about its messages is these four
/// definitions and four proofs; there is no state machine to write.
pub struct CollTok;

impl NetInv<Item> for CollTok {
    open spec fn gate(c: ChanId, s: Seq<Item>, m: Item) -> bool {
        is_hub(c) ==> good(m.v)
    }

    open spec fn wit_inv(c: ChanId, m: Item) -> bool {
        is_hub(c) ==> good(m.v)
    }

    open spec fn deliverable_at(v: Seq<Item>, i: nat) -> bool { fifo_deliverable(v, i) }

    open spec fn extra(sent: Map<ChanId, Seq<Item>>) -> bool { true }

    // This protocol's guarantee is about single messages, so there is
    // nothing for a reader to conclude from a pair.
    open spec fn extra_gives2(c: ChanId, m1: Item, m2: Item) -> bool { true }
    proof fn lemma_extra_gives2(sent: Map<ChanId, Seq<Item>>, c: ChanId,
                                i: nat, j: nat, m1: Item, m2: Item) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<Item>, m: Item) { }
    // No cross-channel obligations: every guarantee here is about one channel.
    open spec fn needs_cause(c: ChanId, m: Item) -> bool { false }
    proof fn lemma_cause_gives(c: ChanId, m: Item, causes: Set<(ChanId, nat, Item)>) { }
    // No cross-channel property to state over the record.
    open spec fn extra_w(was_sent: Set<(ChanId, nat, Item)>) -> bool { true }
    proof fn lemma_extra_w_init() { }

    proof fn lemma_extra_w_preserved(was_sent: Set<(ChanId, nat, Item)>,
                                     c: ChanId, i: nat, m: Item,
                                     causes: Set<(ChanId, nat, Item)>) { }

    proof fn lemma_extra_init(chans: Set<ChanId>) { }
    proof fn lemma_extra_alloc(sent: Map<ChanId, Seq<Item>>, c: ChanId) { }
    proof fn lemma_extra_preserved(sent: Map<ChanId, Seq<Item>>,
                                   was_sent: Set<(ChanId, nat, Item)>,
                                   c: ChanId, s: Seq<Item>, m: Item,
                                   causes: Set<(ChanId, nat, Item)>) { }
}
}

verus!{
// ---------------------------------------------------------------------------
// The two kinds of service.
// ---------------------------------------------------------------------------

/// One producer, emitting on its OWN channel. Send endpoints are not shared:
/// sharing one is exactly what would cost us ownership, and with it the fact
/// that `send` is a left mover.
pub struct Producer {
    pub w:   usize,
    pub hub: Out<Item, CollTok>,
    pub v1:  u64,
    pub v2:  u64,
}

impl Producer {
    pub open spec fn inv(&self) -> bool {
        &&& self.hub.wf()
        &&& 0 <= self.w < n_producers()
        &&& self.hub.id() == hub_from(self.w as int)
        &&& good(self.v1) && good(self.v2)
    }

    /// Two left movers in sequence: one atomic block, no interference point.
    pub fn produce(&mut self)
        requires old(self).inv(),
        ensures  final(self).inv(),
    {
        self.hub.send(Item { v: self.v1 });
        self.hub.send(Item { v: self.v2 });
    }
}

impl Process for Producer {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { self.produce(); }
}

/// The consumer: take whatever turns up first, from whichever producer, and
/// know it is good.
pub struct Consumer {
    pub hub:  Inbox<Item, CollTok>,
    pub last: u64,
}

impl Consumer {
    pub open spec fn inv(&self) -> bool {
        &&& self.hub.wf()
        &&& self.hub.len() == n_producers()
        // Stated over the receiver vector, so it survives a call that changes
        // only the consumption records.
        &&& forall|j: int| 0 <= j < n_producers()
                ==> (#[trigger] self.hub.rxs@[j].id()) == hub_from(j)
    }

    pub fn collect_one(&mut self) -> (item: Item)
        requires old(self).inv(),
        ensures  final(self).inv(), good(item.v),
    {
        proof { hub_config(); }
        // Interference point: producers are emitting while we are blocked.
        let (which, item) = self.hub.recv_any();
        proof {
            let c = self.hub.rxs@[which as int].id();
            assert(c == hub_from(which as int));
            assert(is_hub(c)) by {
                assert(0 <= (which as int) < n_producers()
                       && c == hub_from(which as int));
            }
        }
        item
    }
}

impl Process for Consumer {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) { let it = self.collect_one(); self.last = it.v; }
}
}
