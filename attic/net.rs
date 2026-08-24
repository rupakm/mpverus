// Civl-style message-passing verification for Rust, in Verus.
//
// Core model: the network ghost state records *send histories* (monotone),
// never in-flight buffers (non-monotone). In-flight is derived.

use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

pub type ChanId = nat;

/// Ghost state of one channel: everything ever sent, and everything this
/// channel's (unique) receiver has consumed, in consumption order.
pub struct Chan<M> {
    pub sent: Seq<M>,
    pub recvd: Seq<M>,
}

/// Ghost state of the whole network.
pub struct Net<M> {
    pub chans: Map<ChanId, Chan<M>>,
}

impl<M> Net<M> {
    pub open spec fn dom(self) -> Set<ChanId> { self.chans.dom() }

    pub open spec fn sent(self, c: ChanId) -> Seq<M> { self.chans[c].sent }

    pub open spec fn recvd(self, c: ChanId) -> Seq<M> { self.chans[c].recvd }

    pub open spec fn do_send(self, c: ChanId, m: M) -> Net<M> {
        Net { chans: self.chans.insert(c,
            Chan { sent: self.chans[c].sent.push(m), recvd: self.chans[c].recvd }) }
    }

    pub open spec fn do_recv(self, c: ChanId, m: M) -> Net<M> {
        Net { chans: self.chans.insert(c,
            Chan { sent: self.chans[c].sent, recvd: self.chans[c].recvd.push(m) }) }
    }
}

pub proof fn lemma_do_send_dom<M>(n: Net<M>, c: ChanId, m: M)
    requires n.dom().contains(c)
    ensures  n.do_send(c, m).dom() == n.dom()
{
    assert(n.do_send(c, m).dom() =~= n.dom());
}

pub proof fn lemma_do_recv_dom<M>(n: Net<M>, c: ChanId, m: M)
    requires n.dom().contains(c)
    ensures  n.do_recv(c, m).dom() == n.dom()
{
    assert(n.do_recv(c, m).dom() =~= n.dom());
}

/// Operations on distinct channels commute. These are the generic mover facts
/// every protocol reuses to discharge `Pool`'s locality obligations.
pub proof fn lemma_sends_commute<M>(n: Net<M>, c1: ChanId, m1: M, c2: ChanId, m2: M)
    requires c1 != c2
    ensures  n.do_send(c1, m1).do_send(c2, m2) == n.do_send(c2, m2).do_send(c1, m1)
{
    assert(n.do_send(c1, m1).do_send(c2, m2).chans
        =~= n.do_send(c2, m2).do_send(c1, m1).chans);
}

pub proof fn lemma_send_recv_commute<M>(n: Net<M>, c1: ChanId, m1: M, c2: ChanId, m2: M)
    requires c1 != c2
    ensures  n.do_send(c1, m1).do_recv(c2, m2) == n.do_recv(c2, m2).do_send(c1, m1)
{
    assert(n.do_send(c1, m1).do_recv(c2, m2).chans
        =~= n.do_recv(c2, m2).do_send(c1, m1).chans);
}

pub proof fn lemma_recvs_commute<M>(n: Net<M>, c1: ChanId, m1: M, c2: ChanId, m2: M)
    requires c1 != c2
    ensures  n.do_recv(c1, m1).do_recv(c2, m2) == n.do_recv(c2, m2).do_recv(c1, m1)
{
    assert(n.do_recv(c1, m1).do_recv(c2, m2).chans
        =~= n.do_recv(c2, m2).do_recv(c1, m1).chans);
}

/// Channel semantics, parametric. Both instances share `sent: Seq<M>` as the
/// common denominator; they differ only in which message may be delivered next.
pub trait ChannelModel<M> : Sized {
    /// May `m` be the next message delivered on a channel with this history?
    spec fn deliverable(sent: Seq<M>, recvd: Seq<M>, m: M) -> bool;

    /// Well-formedness of a channel's ghost state.
    spec fn wf(sent: Seq<M>, recvd: Seq<M>) -> bool;

    /// SEND IS A LEFT MOVER: appending to the history never disables a
    /// delivery that was already possible.
    proof fn lemma_send_preserves_deliverable(sent: Seq<M>, recvd: Seq<M>, m: M, m2: M)
        requires Self::deliverable(sent, recvd, m)
        ensures  Self::deliverable(sent.push(m2), recvd, m);

    /// SEND IS A LEFT MOVER (2): appending preserves well-formedness.
    proof fn lemma_send_wf(sent: Seq<M>, recvd: Seq<M>, m2: M)
        requires Self::wf(sent, recvd)
        ensures  Self::wf(sent.push(m2), recvd);

    /// RECV: consuming a deliverable message preserves well-formedness.
    proof fn lemma_recv_wf(sent: Seq<M>, recvd: Seq<M>, m: M)
        requires Self::wf(sent, recvd), Self::deliverable(sent, recvd, m)
        ensures  Self::wf(sent, recvd.push(m));

    /// UNIQUE REPLY: if a channel's whole history is a single message and
    /// nothing has been consumed, delivery is deterministic. This is what lets
    /// the client identify the message `recv_abs` returns with the one the
    /// handler produced.
    proof fn lemma_singleton_delivery(sent: Seq<M>, m: M, r: M)
        requires sent.len() == 1, Self::deliverable(sent, Seq::empty(), m)
        ensures  m == sent[0];

    /// You only ever receive what was actually sent. The bridge from a
    /// delivery back to the send history, and hence to any invariant stated
    /// over that history.
    proof fn lemma_delivered_was_sent(sent: Seq<M>, recvd: Seq<M>, m: M)
        requires Self::deliverable(sent, recvd, m)
        ensures  sent.contains(m);

    /// GATE DISCHARGE for the RPC pattern: if the history is strictly longer
    /// than what has been consumed, *some* message is deliverable. This is what
    /// turns a blocking `recv` into a non-blocking (hence left-moving) one.
    proof fn lemma_nonempty_deliverable(sent: Seq<M>, recvd: Seq<M>)
        requires Self::wf(sent, recvd), recvd.len() < sent.len()
        ensures  exists|m: M| Self::deliverable(sent, recvd, m);
}

/// Per-link FIFO: ChanId is instantiated with (src, dst), so each channel has a
/// unique sender. Order in `sent` is therefore never subject to a race.
pub struct Fifo;

impl<M> ChannelModel<M> for Fifo {
    open spec fn deliverable(sent: Seq<M>, recvd: Seq<M>, m: M) -> bool {
        recvd.len() < sent.len() && sent[recvd.len() as int] == m
    }

    open spec fn wf(sent: Seq<M>, recvd: Seq<M>) -> bool {
        recvd.len() <= sent.len() && recvd =~= sent.take(recvd.len() as int)
    }

    proof fn lemma_send_preserves_deliverable(sent: Seq<M>, recvd: Seq<M>, m: M, m2: M) {
        assert(sent.push(m2)[recvd.len() as int] == sent[recvd.len() as int]);
    }

    proof fn lemma_send_wf(sent: Seq<M>, recvd: Seq<M>, m2: M) {
        assert(sent.push(m2).take(recvd.len() as int) =~= sent.take(recvd.len() as int));
    }

    proof fn lemma_recv_wf(sent: Seq<M>, recvd: Seq<M>, m: M) {
        assert(recvd.push(m) =~= sent.take(recvd.len() as int + 1));
    }

    proof fn lemma_nonempty_deliverable(sent: Seq<M>, recvd: Seq<M>) {
        assert(Self::deliverable(sent, recvd, sent[recvd.len() as int]));
    }

    proof fn lemma_singleton_delivery(sent: Seq<M>, m: M, r: M) {
        assert(Seq::<M>::empty().len() == 0);
    }

    proof fn lemma_delivered_was_sent(sent: Seq<M>, recvd: Seq<M>, m: M) {
        assert(sent[recvd.len() as int] == m);
    }
}

/// Bag (unordered) channel: ChanId is instantiated with the destination, so
/// there may be many concurrent senders -- but bag semantics discards order, so
/// the resulting append race is unobservable.
pub struct Bag;

impl<M> ChannelModel<M> for Bag {
    open spec fn deliverable(sent: Seq<M>, recvd: Seq<M>, m: M) -> bool {
        recvd.push(m).to_multiset().subset_of(sent.to_multiset())
    }

    open spec fn wf(sent: Seq<M>, recvd: Seq<M>) -> bool {
        recvd.to_multiset().subset_of(sent.to_multiset())
    }

    proof fn lemma_send_preserves_deliverable(sent: Seq<M>, recvd: Seq<M>, m: M, m2: M) {
        sent.to_multiset_ensures();
        sent.push(m2).to_multiset_ensures();
        assert forall|x: M| recvd.push(m).to_multiset().count(x)
            <= sent.push(m2).to_multiset().count(x) by {
            assert(sent.push(m2).to_multiset().count(x) >= sent.to_multiset().count(x));
        }
    }

    proof fn lemma_send_wf(sent: Seq<M>, recvd: Seq<M>, m2: M) {
        sent.to_multiset_ensures();
        sent.push(m2).to_multiset_ensures();
        assert forall|x: M| recvd.to_multiset().count(x)
            <= sent.push(m2).to_multiset().count(x) by {
            assert(sent.push(m2).to_multiset().count(x) >= sent.to_multiset().count(x));
        }
    }

    proof fn lemma_recv_wf(sent: Seq<M>, recvd: Seq<M>, m: M) { }

    proof fn lemma_nonempty_deliverable(sent: Seq<M>, recvd: Seq<M>) {
        sent.to_multiset_ensures();
        recvd.to_multiset_ensures();
        // If every element were already fully consumed, the multisets would be
        // equal, contradicting recvd.len() < sent.len().
        if !(exists|m: M| Self::deliverable(sent, recvd, m)) {
            assert forall|x: M| recvd.to_multiset().count(x) == sent.to_multiset().count(x) by {
                if recvd.to_multiset().count(x) < sent.to_multiset().count(x) {
                    recvd.push(x).to_multiset_ensures();
                    assert forall|y: M| recvd.push(x).to_multiset().count(y)
                        <= sent.to_multiset().count(y) by {
                        if y == x {
                        } else {
                            assert(recvd.push(x).to_multiset().count(y)
                                == recvd.to_multiset().count(y));
                        }
                    }
                    assert(Self::deliverable(sent, recvd, x));
                }
            }
            assert(recvd.to_multiset() =~= sent.to_multiset());
        }
    }

    proof fn lemma_delivered_was_sent(sent: Seq<M>, recvd: Seq<M>, m: M) {
        broadcast use vstd::multiset::group_multiset_axioms;
        recvd.to_multiset_ensures();
        assert(recvd.push(m).to_multiset() =~= recvd.to_multiset().insert(m));
        assert(recvd.to_multiset().insert(m).count(m) == recvd.to_multiset().count(m) + 1);
        assert(recvd.push(m).to_multiset().count(m) > 0);
        assert(sent.to_multiset().count(m) > 0);
        vstd::seq_lib::to_multiset_contains(sent, m);
    }

    proof fn lemma_singleton_delivery(sent: Seq<M>, m: M, r: M) {
        broadcast use vstd::multiset::group_multiset_axioms;
        let e = Seq::<M>::empty();
        e.to_multiset_ensures();
        vstd::multiset::lemma_multiset_empty_len(e.to_multiset());
        assert(e.to_multiset() =~= Multiset::<M>::empty());
        e.push(m).to_multiset_ensures();
        assert(e.push(m).to_multiset().count(m) == 1);
        assert(sent =~= e.push(sent[0]));
        e.push(sent[0]).to_multiset_ensures();
        if m != sent[0] {
            assert(sent.to_multiset().count(m) == 0);
        }
    }
}

/// Lossy, duplicating bag: an unreliable datagram network. A message that was
/// ever sent may be delivered any number of times (duplication), and nothing
/// ever forces a delivery (loss). Delivery no longer consumes: `recvd` is a
/// log of what arrived, not a debit against `sent`.
///
/// Note what does NOT change. `send` is still a left mover, because
/// `deliverable` is still monotone in `sent`. What changes is the strength of
/// the facts a receiver gets: `lemma_delivered_was_sent` still holds --- so any
/// invariant of the form "everything ever sent satisfies P" survives verbatim
/// --- but nothing bounds how often a message arrives, so counting arguments
/// ("I have collected n distinct votes") no longer go through. Protocols that
/// need them must re-establish uniqueness themselves, e.g. by tagging messages
/// with sequence numbers and discarding duplicates.
pub struct LossyBag;

impl<M> ChannelModel<M> for LossyBag {
    open spec fn deliverable(sent: Seq<M>, recvd: Seq<M>, m: M) -> bool {
        sent.contains(m)
    }

    open spec fn wf(sent: Seq<M>, recvd: Seq<M>) -> bool {
        forall|x: M| recvd.contains(x) ==> #[trigger] sent.contains(x)
    }

    proof fn lemma_send_preserves_deliverable(sent: Seq<M>, recvd: Seq<M>, m: M, m2: M) {
        lemma_push_contains(sent, m, m2);
    }

    proof fn lemma_send_wf(sent: Seq<M>, recvd: Seq<M>, m2: M) {
        assert forall|x: M| recvd.contains(x) implies #[trigger] sent.push(m2).contains(x) by {
            lemma_push_contains(sent, x, m2);
        }
    }

    proof fn lemma_recv_wf(sent: Seq<M>, recvd: Seq<M>, m: M) {
        assert forall|x: M| recvd.push(m).contains(x) implies #[trigger] sent.contains(x) by {
            let i = choose|i: int| 0 <= i < recvd.push(m).len() && recvd.push(m)[i] == x;
            if i < recvd.len() {
                assert(recvd[i] == x);
            }
        }
    }

    proof fn lemma_nonempty_deliverable(sent: Seq<M>, recvd: Seq<M>) {
        assert(sent.contains(sent[0]));
        assert(Self::deliverable(sent, recvd, sent[0]));
    }

    proof fn lemma_singleton_delivery(sent: Seq<M>, m: M, r: M) {
        let i = choose|i: int| 0 <= i < sent.len() && sent[i] == m;
    }

    proof fn lemma_delivered_was_sent(sent: Seq<M>, recvd: Seq<M>, m: M) { }
}

/// `push` never removes an element.
pub proof fn lemma_push_contains<M>(s: Seq<M>, x: M, y: M)
    requires s.contains(x)
    ensures  s.push(y).contains(x)
{
    let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
    assert(s.push(y)[i] == x);
}

} // verus!
