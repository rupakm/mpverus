// The library: channel naming, the network state machine, the trusted channel
// primitives, and the operations built on them.
//
// The network state is not one shared object. It is divided into pieces, each
// owned by exactly one thread, so that a fact about a piece is stable because
// nobody else can change it rather than because an invariant says so.
//
// There is ONE state machine, `NetSM`, parameterised by the protocol running on
// it. A protocol supplies a message type and an implementation of `NetInv`,
// which says what a send must satisfy and what may be concluded about a message
// that was sent. It writes no state machine of its own.
//
// A protocol that needs ghost state of its own -- a phase counter, a record of
// local decisions -- declares a separate state machine for it. The two are
// independent instances, so a token of one cannot affect the other and no
// obligation relates them. The exception is protocol state that must be related
// to network state; that has to live in one machine, and is not expressible
// here.
//
// The contents, in order:
//
//   * channel names, and the lemmas that make distinct names provably distinct;
//   * `NetInv`, the interface a protocol implements, and `DetDelivery` for
//     protocols whose delivery is deterministic;
//   * `NetSM`, the network state machine;
//   * the trusted primitives `send`, `recv`, `recv_any` and `make_endpoints`;
//   * verified operations usable by any protocol: `recv_learn`, `recv_abs`,
//     `mint`, `absorb_handler` and `rpc`.

use vstd::prelude::*;
use vstd::tokens::{InstanceId, KeyValueToken, ElementToken, MapToken, SetToken};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;

verus! {

/// A channel name: a family tag together with indices within that family.
///
/// Protocols need to know that distinct participants have distinct channels,
/// and that a request channel is never a reply channel. Giving names structure
/// makes both of these consequences of structural equality, so a protocol
/// builds its names with `chan` and proves distinctness rather than assuming
/// it. Requests are conventionally family 0 and replies family 1; the indices
/// say which participant, and for a per-call channel, which call.
pub struct ChanId {
    /// Which family of channels this belongs to: requests, replies, ring
    /// links, and so on. Distinct tags are distinct channels, always.
    pub fam: nat,
    /// Indices within the family -- a participant number, a call counter.
    pub ix: Seq<int>,
}

/// Build a channel name. Injective in both arguments by construction.
pub open spec fn chan(fam: nat, ix: Seq<int>) -> ChanId {
    ChanId { fam, ix }
}

/// Within one family, one index: names are equal only if the index is.
pub proof fn lemma_chan_inj1(f: nat, a: int, b: int)
    requires
        chan(f, seq![a]) == chan(f, seq![b]),
    ensures
        a == b,
{
    assert(seq![a][0] == a);
    assert(seq![b][0] == b);
}

/// Within one family, two indices.
pub proof fn lemma_chan_inj2(f: nat, a1: int, a2: int, b1: int, b2: int)
    requires
        chan(f, seq![a1, a2]) == chan(f, seq![b1, b2]),
    ensures
        a1 == b1 && a2 == b2,
{
    assert(seq![a1, a2][0] == a1);
    assert(seq![b1, b2][0] == b1);
    assert(seq![a1, a2][1] == a2);
    assert(seq![b1, b2][1] == b2);
}

/// Two names built from the same family and indices are the same name, and
/// otherwise they differ. Stated as a lemma because sequence equality needs
/// extensionality, which is the one step Verus will not take unprompted.
pub proof fn lemma_chan_distinct(f1: nat, i1: Seq<int>, f2: nat, i2: Seq<int>)
    requires
        f1 != f2 || !(i1 =~= i2),
    ensures
        chan(f1, i1) != chan(f2, i2),
{
    if f1 == f2 {
        assert(!(i1 =~= i2));
    }
}

// The running channel types. Verus has no specification for these, and needs
// none: the proof speaks only about a channel's name and the token for it.
// Declaring them opaque lets the endpoint structs carry a real channel while
// staying ordinary Verus types.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMpscSender<#[verifier::reject_recursive_types] M>(std::sync::mpsc::Sender<M>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMpscReceiver<#[verifier::reject_recursive_types] M>(std::sync::mpsc::Receiver<M>);

/// Send endpoint. A channel's send history is exclusively owned by its unique
/// sender, so this is deliberately not duplicable: sharing it would cost that
/// ownership and, with it, the fact that `send` is a left mover. Several
/// producers are modelled as a family of channels instead; see
/// `collector.rs`.
/// The fields are private and the type is opaque to Verus, which matters for
/// soundness rather than tidiness. With them public, verified code could take a
/// handle whose real queue belongs to one channel and rebuild it carrying
/// another channel's name; a send would then satisfy every precondition, record
/// one channel's history growing, and put the bytes in a different queue. The
/// receiver on that queue would be handed a message that `recv`'s postcondition
/// asserts was sent on its own channel, and was not. Nothing else in the
/// development would notice.
///
/// `id` is therefore readable only through a specification function, and only
/// `make_endpoints` can produce a handle at all.
#[verifier::external_body]
pub struct Sender<#[verifier::reject_recursive_types] M> {
    id: Ghost<ChanId>,
    /// The running channel. Present in the compiled program and irrelevant to
    /// the proof, which speaks only about `id()`.
    inner: std::sync::mpsc::Sender<M>,
}

impl<M> Sender<M> {
    /// The channel this handle names. Fixed when the handle was made.
    pub uninterp spec fn id(&self) -> ChanId;
}

/// Receive endpoint. Deliberately not `Clone`, so that Rust's ownership rules
/// supply the single-consumer condition the proof requires.
/// The dual, and opaque for the same reason.
#[verifier::external_body]
pub struct Receiver<#[verifier::reject_recursive_types] M> {
    id: Ghost<ChanId>,
    inner: std::sync::mpsc::Receiver<M>,
}

impl<M> Receiver<M> {
    pub uninterp spec fn id(&self) -> ChanId;
}


/// Per-link FIFO delivery: the next message is the one at the current length.
pub open spec fn fifo_deliverable<M>(v: Seq<M>, i: nat) -> bool { i == v.len() }

/// A channel created while the program runs: family `fam`, owner `j`, and the
/// value the allocator had when it was created. Channels named with two indices
/// are reserved for this; a protocol's static channels use none or one.
pub open spec fn dyn_chan(fam: nat, j: int, k: nat) -> ChanId {
    chan(fam, seq![j, k as int])
}

// ---------------------------------------------------------------------------
// What a protocol says about its messages.
//
// This is the whole interface. A protocol implements it and writes no state
// machine: `NetSM` below is shared by every protocol and reads the protocol
// through this trait.
// ---------------------------------------------------------------------------
pub trait NetInv<M> : Sized {
    /// The states from which a send must not FAIL. This is Civl's rho, and it
    /// is distinct from blocking: a send whose gate does not hold is a bug in
    /// the program, whereas an operation with no available step merely waits.
    spec fn gate(c: ChanId, s: Seq<M>, m: M) -> bool;

    /// What is guaranteed about a message that was sent on a channel. For most
    /// protocols this is the same predicate as the gate: the gate says what may
    /// be placed on a channel, and this says everything there satisfies it.
    spec fn wit_inv(c: ChanId, m: M) -> bool;

    /// Which index may be delivered next, given what has been consumed. Per
    /// link FIFO says `fifo_deliverable`; an unreliable link says `true`.
    spec fn deliverable_at(v: Seq<M>, i: nat) -> bool;

    /// An invariant over the send HISTORIES, for a guarantee that no single
    /// message can express -- an ordering between messages, say.
    ///
    /// Use this when the property needs the sequence: an ordered journal,
    /// increasing sequence numbers. For a property that merely says some
    /// message exists on another channel, use `record_inv` below, which is far
    /// cheaper to preserve. Most protocols leave both `true`.
    spec fn history_inv(sent: Map<ChanId, Seq<M>>) -> bool;

    /// What a reader may conclude about TWO messages it holds witnesses for,
    /// given `history_inv`. This is how a pairwise guarantee is CONSUMED.
    ///
    /// It must mention only `c`, `m1` and `m2`, for the same reason
    /// `cause_gives` must be pure: the histories are reached through a binding
    /// the reader cannot name, so anything said about them is projected away.
    ///
    /// Most protocols leave this `true`; a protocol whose guarantee is about
    /// pairs -- heartbeat's increasing sequence numbers -- states it here.
    spec fn pair_gives(c: ChanId, m1: M, m2: M) -> bool;

    /// Two messages at known positions of one channel's history satisfy it.
    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<M>>, c: ChanId,
                                i: nat, j: nat, m1: M, m2: M)
        requires
            Self::history_inv(sent),
            sent.dom().contains(c),
            i < j < sent[c].len(),
            sent[c][i as int] == m1,
            sent[c][j as int] == m2,
        ensures
            Self::pair_gives(c, m1, m2);

    /// The gate is strong enough to establish the guarantee for the message it
    /// admits. Immediate when the two are the same predicate.
    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<M>, m: M)
        requires Self::gate(c, s, m)
        ensures  Self::wit_inv(c, m);

    /// Does sending `m` on `c` require pointing at a message already sent
    /// somewhere else? A gate can only inspect its own channel's history, so a
    /// requirement that reaches across channels is stated here instead.
    ///
    /// Defaults to false: a protocol that relates messages on a single channel
    /// says nothing and uses `send` throughout.
    open spec fn needs_cause(c: ChanId, m: M) -> bool { false }

    /// Are the messages in `causes` acceptable justification for sending `m` on
    /// `c`? Each element is a channel, a position, and the message sent there.
    ///
    /// A set rather than a single message, because a decision may rest on
    /// several: a coordinator committing needs every vote, not one.
    open spec fn caused_by(c: ChanId, m: M, causes: Set<(ChanId, nat, M)>) -> bool { false }

    /// What a thread may conclude about `m` from the fact that a justification
    /// for it exists. This must mention only `c` and `m`: the justifying
    /// message is reached by an existential that the reader cannot name, so
    /// anything said about it directly is lost. The point of this predicate is
    /// to carry the content of that existential across, in a form the reader
    /// can use.
    open spec fn cause_gives(c: ChanId, m: M) -> bool { true }

    /// A justification really does establish it. The justifying message is
    /// known to satisfy the protocol's guarantee, because everything ever sent
    /// does; that is what makes this provable rather than assumed.
    proof fn lemma_cause_gives(c: ChanId, m: M, causes: Set<(ChanId, nat, M)>)
        requires
            Self::needs_cause(c, m),
            Self::caused_by(c, m, causes),
            forall|e: (ChanId, nat, M)| causes.contains(e) ==> Self::wit_inv(e.0, e.2),
        ensures
            Self::cause_gives(c, m),
        ;

    /// The additional invariant holds of the initial state ...
    proof fn lemma_history_inv_init(chans: Set<ChanId>)
        ensures Self::history_inv(Map::new(chans, |c: ChanId| Seq::<M>::empty()));

    /// ... is preserved by creating a fresh, empty channel ...
    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<M>>, c: ChanId)
        requires
            Self::history_inv(sent),
            !sent.dom().contains(c),
        ensures
            Self::history_inv(sent.insert(c, Seq::<M>::empty()));

    /// An invariant over the RECORD of what was sent, as opposed to over the
    /// histories.
    ///
    /// This is the right home for a protocol-global property that relates
    /// messages on different channels. `history_inv` is stated over `sent`, a map of
    /// sequences that changes structurally at every send, so preserving a
    /// cross-channel property there means reasoning about a map insertion and
    /// sequence indices at each step. `was_sent` only grows, so preservation
    /// here is only ever about the ONE element just added.
    ///
    /// Measured on the same property, stated both ways: two lines of inductive
    /// step against twenty-one.
    ///
    /// Use `history_inv` for a property of one channel's ORDER -- an ordered journal,
    /// increasing sequence numbers -- which needs the sequence. Use this for a
    /// property that says some message exists somewhere else.
    spec fn record_inv(was_sent: Set<(ChanId, nat, M)>) -> bool;

    /// It holds of the empty record.
    proof fn lemma_record_inv_init()
        ensures Self::record_inv(Set::empty());

    /// Preserved by adding one element to the record. The witnesses the sender
    /// presented are available, which is what makes a cross-channel property
    /// provable at all.
    proof fn lemma_record_inv_preserved(
        was_sent: Set<(ChanId, nat, M)>,
        sent: Map<ChanId, Seq<M>>,
        c: ChanId, s: Seq<M>, m: M,
        causes: Set<(ChanId, nat, M)>,
    )
        requires
            Self::record_inv(was_sent),
            // The gate and the history it read, so a property of the record
            // may still be established from what the gate checked. Without
            // this, "no earlier message on this channel had property P" is
            // unavailable, and that is a thing gates routinely enforce.
            Self::gate(c, s, m),
            sent.dom().contains(c), sent[c] == s,
            // A witness names a real position of a real history, which is what
            // ties the two domains together.
            forall|k: ChanId, i2: nat, mm: M| (#[trigger] was_sent.contains((k, i2, mm)))
                ==> sent.dom().contains(k) && i2 < sent[k].len() && sent[k][i2 as int] == mm,
            causes.subset_of(was_sent),
            Self::needs_cause(c, m) ==> Self::caused_by(c, m, causes),
        ensures
            Self::record_inv(was_sent.insert((c, s.len(), m)));

    /// ... and is preserved by a send the gate admits.
    ///
    /// This lemma is handed everything the machine knows at the moment of the
    /// send, not just the gate. A guarantee about ONE channel needs only the
    /// gate; a guarantee relating messages on DIFFERENT channels cannot be
    /// preserved from the gate alone, because a gate reads one history. What
    /// makes such a guarantee provable is the same thing that makes the send
    /// legal in the first place: the witnesses the sender presented. So they
    /// are passed in, together with the record they came from and the machine's
    /// agreement invariant relating that record to the histories.
    ///
    /// Paxos is the protocol that forced this. Its safety argument is about
    /// messages on many acceptors' channels, and the reason a proposer may send
    /// `Accept(b, v)` is precisely the quorum of promises it holds witnesses
    /// for. With only the gate available, that argument cannot be made.
    proof fn lemma_history_inv_preserved(
        sent: Map<ChanId, Seq<M>>,
        was_sent: Set<(ChanId, nat, M)>,
        c: ChanId, s: Seq<M>, m: M,
        causes: Set<(ChanId, nat, M)>,
    )
        requires
            Self::history_inv(sent), Self::gate(c, s, m),
            sent.dom().contains(c), sent[c] == s,
            // The machine's agreement invariant: a witness names a real
            // position of a real history.
            forall|k: ChanId, i: nat, mm: M| (#[trigger] was_sent.contains((k, i, mm)))
                ==> sent.dom().contains(k) && i < sent[k].len() && sent[k][i as int] == mm,
            // The witnesses the sender presented, and what they justify.
            causes.subset_of(was_sent),
            Self::needs_cause(c, m) ==> Self::caused_by(c, m, causes),
        ensures
            Self::history_inv(sent.insert(c, s.push(m)));
}

/// Protocols whose delivery is deterministic: at most one index is deliverable
/// from a given consumption record, so a witness for that position determines
/// the message that will arrive.
///
/// This is what `recv_abs`, and therefore `rpc`, requires, and it is not
/// available on every channel. An unreliable link may deliver any index at any
/// time and cannot implement it, which is what prevents a remote call being
/// written against such a link.
pub trait DetDelivery<M> : NetInv<M> {
    proof fn lemma_delivery_determined(v: Seq<M>, i: nat, j: nat)
        requires Self::deliverable_at(v, i), Self::deliverable_at(v, j)
        ensures  i == j;
}

/// A justification found in a record stays valid in any larger record. This is
/// why provenance is stable under interference: `was_sent` only grows, so no
/// step of any thread can remove the messages a justification points at.
pub proof fn lemma_cause_persists<M, Inv: NetInv<M>>(
    old: Set<(ChanId, nat, M)>, new: Set<(ChanId, nat, M)>, c: ChanId, m: M,
)
    requires
        old.subset_of(new),
        exists|causes: Set<(ChanId, nat, M)>|
            causes.subset_of(old) && Inv::caused_by(c, m, causes),
    ensures
        exists|causes: Set<(ChanId, nat, M)>|
            causes.subset_of(new) && Inv::caused_by(c, m, causes),
{
    let causes = choose|causes: Set<(ChanId, nat, M)>|
        causes.subset_of(old) && Inv::caused_by(c, m, causes);
    assert(causes.subset_of(new));
}

/// Per-link FIFO delivery is deterministic. One call discharges the obligation
/// for any protocol that selects `fifo_deliverable`.
pub proof fn lemma_fifo_determined<M>(v: Seq<M>, i: nat, j: nat)
    requires fifo_deliverable(v, i), fifo_deliverable(v, j)
    ensures  i == j,
{
}

} // verus!

// ---------------------------------------------------------------------------
// The network state machine shared by every protocol.
//
// `sent` and `recvd` are divided per channel and exclusively owned: a channel's
// send history belongs to its sender, its consumption record to its receiver.
// `was_sent` is persistent -- its tokens are duplicable and never retracted --
// and is how a receiver learns about a history it does not own. `next` is the
// allocator for channels created while the program runs.
// ---------------------------------------------------------------------------
tokenized_state_machine!{
    NetSM<M, Inv: NetInv<M>> {
        fields {
            #[sharding(map)]            pub sent:  Map<ChanId, Seq<M>>,
            #[sharding(map)]            pub recvd: Map<ChanId, Seq<M>>,
            #[sharding(persistent_set)] pub was_sent: Set<(ChanId, nat, M)>,
            #[sharding(variable)]       pub next: nat,
            /// Carries the protocol parameter; see `rwlock.rs` for the idiom.
            #[sharding(constant)]       pub inv: PhantomData<Inv>,
        }

        /// A witness describes the history it refers to.
        #[invariant]
        pub spec fn agree(&self) -> bool {
            forall|c: ChanId, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> self.sent.dom().contains(c)
                    && i < self.sent[c].len() && self.sent[c][i as int] == m
        }

        /// The protocol's guarantee about everything ever sent. Stated over
        /// `was_sent`, which only grows, so no other thread can falsify it.
        #[invariant]
        pub spec fn protocol_inv(&self) -> bool {
            forall|c: ChanId, i: nat, m: M| #[trigger] self.was_sent.contains((c, i, m))
                ==> Inv::wit_inv(c, m)
        }

        /// The protocol's additional invariant, if it has one.
        /// Every message that needed a cause has one. The existential ranges
        /// over `was_sent`, which only grows, so once established for a message
        /// it stays established no matter what any other thread does.
        #[invariant]
        pub spec fn provenance(&self) -> bool {
            forall|c: ChanId, i: nat, m: M|
                (#[trigger] self.was_sent.contains((c, i, m))) && Inv::needs_cause(c, m)
                    ==> exists|causes: Set<(ChanId, nat, M)>|
                            causes.subset_of(self.was_sent) && Inv::caused_by(c, m, causes)
        }

        #[invariant]
        pub spec fn protocol_extra_w(&self) -> bool { Inv::record_inv(self.was_sent) }

        #[invariant]
        pub spec fn protocol_extra(&self) -> bool { Inv::history_inv(self.sent) }

        /// Nothing at or above the allocator's counter exists yet. This is what
        /// makes creating a channel sound without anyone seeing the whole
        /// domain.
        #[invariant]
        pub spec fn unallocated(&self) -> bool {
            forall|f: nat, j: int, k: nat| k >= self.next
                ==> !self.sent.dom().contains(#[trigger] dyn_chan(f, j, k))
                 && !self.recvd.dom().contains(dyn_chan(f, j, k))
        }

        init!{
            boot(chans: Set<ChanId>) {
                // Channels named with two indices are reserved for allocation.
                require(forall|f: nat, j: int, k: nat|
                    !chans.contains(#[trigger] dyn_chan(f, j, k)));
                init sent     = Map::new(chans, |c: ChanId| Seq::<M>::empty());
                init recvd    = Map::new(chans, |c: ChanId| Seq::<M>::empty());
                init was_sent = Set::empty();
                init next     = 0;
                init inv      = PhantomData;
            }
        }

        transition!{
            do_send(c: ChanId, s: Seq<M>, m: M, causes: Set<(ChanId, nat, M)>) {
                remove sent -= [c => s];
                // The sender must hold a witness for every message it points
                // at. This is what stops a justification being invented.
                have   was_sent >= (causes);
                require(Inv::gate(c, s, m));
                require(Inv::needs_cause(c, m) ==> Inv::caused_by(c, m, causes));
                add    sent += [c => s.push(m)];
                add    was_sent (union)= set { (c, s.len(), m) };
            }
        }

        transition!{
            do_recv(c: ChanId, r: Seq<M>, i: nat, m: M) {
                remove recvd -= [c => r];
                have   was_sent >= set { (c, i, m) };
                require(Inv::deliverable_at(r, i));
                add    recvd += [c => r.push(m)];
            }
        }

        /// Create a channel. Freshness is proved from `unallocated`, not
        /// assumed.
        transition!{
            alloc(fam: nat, j: int) {
                add    sent  += [dyn_chan(fam, j, pre.next) => Seq::<M>::empty()];
                add    recvd += [dyn_chan(fam, j, pre.next) => Seq::<M>::empty()];
                update next = pre.next + 1;
            }
        }

        /// How a thread turns a witness into the protocol's guarantee.
        property!{
            learn(c: ChanId, i: nat, m: M) {
                have was_sent >= set { (c, i, m) };
                assert(Inv::wit_inv(c, m));
            }
        }

        /// How a thread recovers a cross-channel fact. It holds a witness for
        /// `m` alone, and learns that somewhere a justifying message was sent.
        ///
        /// The `birds_eye` binding reads the whole record, which a thread does
        /// not own. That is sound because `was_sent` only grows: a fact read
        /// this way cannot be falsified by a later step of any thread. What the
        /// caller receives is the existential with the record projected out.
        property!{
            learn_cause(c: ChanId, i: nat, m: M) {
                have was_sent >= set { (c, i, m) };
                require(Inv::needs_cause(c, m));
                birds_eye let ws = pre.was_sent;
                assert(Inv::cause_gives(c, m)) by {
                    let causes = choose|causes: Set<(ChanId, nat, M)>|
                        causes.subset_of(ws) && Inv::caused_by(c, m, causes);
                    assert(causes.subset_of(ws));
                    assert forall|e: (ChanId, nat, M)| causes.contains(e)
                        implies Inv::wit_inv(e.0, e.2) by {
                        assert(causes.subset_of(ws));
                        assert(ws.contains((e.0, e.1, e.2)));
                    }
                    Inv::lemma_cause_gives(c, m, causes);
                };
            }
        }

        /// How a thread uses a guarantee about PAIRS of messages on a channel it
        /// does not own. Two witnesses in, a pure fact about the two messages
        /// out.
        ///
        /// Reading `sent` here is sound even though `sent` is not monotone,
        /// because what leaves is a pure predicate about two messages, and a
        /// pure fact cannot later become false. Retaining anything about the
        /// histories themselves would not be sound, and the binding going out
        /// of scope is what prevents it.
        property!{
            learn_pair(c: ChanId, i: nat, j: nat, m1: M, m2: M) {
                have was_sent >= set { (c, i, m1) };
                have was_sent >= set { (c, j, m2) };
                require(i < j);
                birds_eye let s = pre.sent;
                assert(Inv::pair_gives(c, m1, m2)) by {
                    Inv::lemma_pair_gives(s, c, i, j, m1, m2);
                };
            }
        }

        /// Two witnesses for the same position name the same message. This is
        /// the agreement invariant read twice.
        property!{
            witness_agree(c: ChanId, i: nat, m1: M, m2: M) {
                have was_sent >= set { (c, i, m1) };
                have was_sent >= set { (c, i, m2) };
                assert(m1 == m2);
            }
        }

        #[inductive(boot)]
        fn boot_inductive(post: Self, chans: Set<ChanId>) {
            Inv::lemma_history_inv_init(chans);
            Inv::lemma_record_inv_init();
        }

        #[inductive(do_send)]
        fn do_send_inductive(
            pre: Self, post: Self,
            c: ChanId, s: Seq<M>, m: M, causes: Set<(ChanId, nat, M)>,
        ) {
            Inv::lemma_gate_gives_inv(c, s, m);
            Inv::lemma_history_inv_preserved(pre.sent, pre.was_sent, c, s, m, causes);
            Inv::lemma_record_inv_preserved(pre.was_sent, pre.sent, c, s, m, causes);
            assert(post.was_sent =~= pre.was_sent.insert((c, s.len(), m)));
            assert(post.sent =~= pre.sent.insert(c, s.push(m)));
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                implies post.sent.dom().contains(k)
                    && i < post.sent[k].len() && post.sent[k][i as int] == mm by {
                if (k, i, mm) != (c, s.len(), m) { assert(pre.was_sent.contains((k, i, mm))); }
                if k == c { assert(post.sent[c] == s.push(m)); }
            }
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                implies Inv::wit_inv(k, mm) by {
                if (k, i, mm) != (c, s.len(), m) { assert(pre.was_sent.contains((k, i, mm))); }
            }
            assert forall|f: nat, jj: int, k: nat| k >= post.next
                implies !post.sent.dom().contains(#[trigger] dyn_chan(f, jj, k))
                     && !post.recvd.dom().contains(dyn_chan(f, jj, k)) by {
                assert(post.sent.dom() =~= pre.sent.dom());
            }
            // Provenance. The justification the sender presented is in the
            // record, because the transition's `have` required it; and every
            // earlier justification survives, because the record only grows.
            assert(pre.was_sent.subset_of(post.was_sent));
            assert forall|k: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((k, i, mm))
                && Inv::needs_cause(k, mm)
                implies exists|cs: Set<(ChanId, nat, M)>|
                    cs.subset_of(post.was_sent) && Inv::caused_by(k, mm, cs) by {
                if (k, i, mm) == (c, s.len(), m) {
                    assert(causes.subset_of(post.was_sent) && Inv::caused_by(k, mm, causes));
                } else {
                    assert(pre.was_sent.contains((k, i, mm)));
                    lemma_cause_persists::<M, Inv>(pre.was_sent, post.was_sent, k, mm);
                }
            }
        }

        #[inductive(do_recv)]
        fn do_recv_inductive(pre: Self, post: Self, c: ChanId, r: Seq<M>, i: nat, m: M) {
            assert forall|f: nat, jj: int, k: nat| k >= post.next
                implies !post.sent.dom().contains(#[trigger] dyn_chan(f, jj, k))
                     && !post.recvd.dom().contains(dyn_chan(f, jj, k)) by {
                assert(post.recvd.dom() =~= pre.recvd.dom());
            }
        }

        #[inductive(alloc)]
        fn alloc_inductive(pre: Self, post: Self, fam: nat, j: int) {
            assert forall|f: nat, jj: int, k: nat| k >= post.next
                implies !post.sent.dom().contains(#[trigger] dyn_chan(f, jj, k))
                     && !post.recvd.dom().contains(dyn_chan(f, jj, k)) by {
                assert(k != pre.next);
                assert(!(seq![jj, k as int] =~= seq![j, pre.next as int])) by {
                    assert(seq![jj, k as int][1] == k as int);
                    assert(seq![j, pre.next as int][1] == pre.next as int);
                }
                lemma_chan_distinct(f, seq![jj, k as int], fam, seq![j, pre.next as int]);
            }
            assert(post.sent =~= pre.sent
                .insert(dyn_chan(fam, j, pre.next), Seq::<M>::empty()));
            Inv::lemma_history_inv_alloc(pre.sent, dyn_chan(fam, j, pre.next));
            assert forall|c: ChanId, i: nat, mm: M| #[trigger] post.was_sent.contains((c, i, mm))
                implies post.sent.dom().contains(c)
                    && i < post.sent[c].len() && post.sent[c][i as int] == mm by {
                assert(pre.was_sent.contains((c, i, mm)));
                assert(c != dyn_chan(fam, j, pre.next));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The trusted channel primitives. Their specifications are the state machine's
// transitions; the runtime that implements them is not verified.
// ---------------------------------------------------------------------------
verus!{

/// The one send primitive, and a left mover. It changes a token no other
/// thread can hold, so no other thread's step can observe the change; and it
/// adds an element to a persistent set, which commutes with every other action
/// and can only enable a later one, never disable it.
///
/// `causes` carries the witnesses for whatever messages this one is required to
/// point at. Holding them is what makes a cross-channel requirement checkable
/// without reading state the sender does not own. Protocols that relate
/// messages only within a channel pass no causes and use `send` below.
#[verifier::external_body]
pub fn send_general<M, Inv: NetInv<M>>(
    s: &Sender<M>, m: M,
    Tracked(inst):   Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):    Tracked<&mut NetSM::sent<M, Inv>>,
    Tracked(causes): Tracked<&SetToken<(ChanId, nat, M), NetSM::was_sent<M, Inv>>>,
) -> (w: Tracked<NetSM::was_sent<M, Inv>>)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == s.id(),
        Inv::gate(s.id(), old(tok).value(), m),          // the gate
        causes.instance_id() == inst.id(),
        Inv::needs_cause(s.id(), m) ==> Inv::caused_by(s.id(), m, causes.set()),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == s.id(),
        final(tok).value() == old(tok).value().push(m),
        w@.instance_id() == inst.id(),
        w@.element() == (s.id(), old(tok).value().len(), m),
{
    // A closed receiver means the peer is gone; the proof assumes it is not.
    s.inner.send(m).unwrap();
    Tracked::assume_new()
}

/// A send of a message that needs no justification. Verified, not assumed: it
/// is `send_general` with the empty set of causes.
pub fn send<M, Inv: NetInv<M>>(
    s: &Sender<M>, m: M,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):  Tracked<&mut NetSM::sent<M, Inv>>,
) -> (w: Tracked<NetSM::was_sent<M, Inv>>)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == s.id(),
        Inv::gate(s.id(), old(tok).value(), m),
        !Inv::needs_cause(s.id(), m),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == s.id(),
        final(tok).value() == old(tok).value().push(m),
        w@.instance_id() == inst.id(),
        w@.element() == (s.id(), old(tok).value().len(), m),
{
    let tracked none;
    proof { none = SetToken::empty(inst.id()); }
    send_general::<M, Inv>(s, m, Tracked(inst), Tracked(tok), Tracked(&none))
}

/// A send justified by exactly one earlier message. Verified: it packages the
/// single witness into a set and defers to `send_general`.
pub fn send_caused<M, Inv: NetInv<M>>(
    s: &Sender<M>, m: M,
    Tracked(inst):  Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):   Tracked<&mut NetSM::sent<M, Inv>>,
    Tracked(cause): Tracked<&NetSM::was_sent<M, Inv>>,
) -> (w: Tracked<NetSM::was_sent<M, Inv>>)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == s.id(),
        Inv::gate(s.id(), old(tok).value(), m),
        cause.instance_id() == inst.id(),
        Inv::caused_by(s.id(), m, set![cause.element()]),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key()   == s.id(),
        final(tok).value() == old(tok).value().push(m),
        w@.instance_id() == inst.id(),
        w@.element() == (s.id(), old(tok).value().len(), m),
{
    let tracked one;
    proof {
        // Witnesses are duplicable, so borrowing one is enough to build the set.
        let tracked mut acc = SetToken::empty(inst.id());
        acc.insert(*cause);
        assert(acc.set() =~= set![cause.element()]);
        one = acc;
    }
    send_general::<M, Inv>(s, m, Tracked(inst), Tracked(tok), Tracked(&one))
}

/// A blocking receive: a right mover, and an interference point. It returns a
/// witness that what arrived was sent, which is the receiver's only source of
/// knowledge about a history it does not own.
#[verifier::external_body]
pub fn recv<M, Inv: NetInv<M>>(
    r: &Receiver<M>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):  Tracked<&mut NetSM::recvd<M, Inv>>,
) -> (res: (M, Tracked<NetSM::was_sent<M, Inv>>))
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == r.id(),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key() == r.id(),
        res.1@.instance_id() == inst.id(),
        res.1@.element().0 == r.id(),
        res.1@.element().2 == res.0,
        Inv::deliverable_at(old(tok).value(), res.1@.element().1),
        final(tok).value() == old(tok).value().push(res.0),
{
    let m = r.inner.recv().unwrap();
    (m, Tracked::assume_new())
}

/// Block until a message arrives on any of these channels, and report which
/// channel produced it.
///
/// Unordered delivery from several senders is modelled as a family of
/// per-sender channels rather than one channel with many senders. A single
/// history with several concurrent appenders cannot be exclusively owned, and
/// without exclusive ownership `send` is not a left mover. Dividing by sender
/// restores ownership and retains per-sender order, which a real
/// multi-producer channel also retains.
#[verifier::external_body]
pub fn recv_any<M, Inv: NetInv<M>>(
    rxs: &Vec<Receiver<M>>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(map):  Tracked<&mut MapToken<ChanId, Seq<M>, NetSM::recvd<M, Inv>>>,
) -> (res: (usize, M, Tracked<NetSM::was_sent<M, Inv>>))
    requires
        rxs.len() > 0,
        old(map).instance_id() == inst.id(),
        forall|j: int| 0 <= j < rxs.len() ==> old(map).dom().contains(#[trigger] rxs[j].id()),
    ensures
        0 <= res.0 < rxs.len(),
        res.2@.instance_id() == inst.id(),
        res.2@.element().0 == rxs[res.0 as int].id(),
        res.2@.element().2 == res.1,
        final(map).instance_id() == old(map).instance_id(),
        final(map).dom() == old(map).dom(),
        forall|c: ChanId| old(map).dom().contains(c) && c != rxs[res.0 as int].id()
            ==> #[trigger] final(map).map()[c] == old(map).map()[c],
        Inv::deliverable_at(old(map).map()[rxs[res.0 as int].id()], res.2@.element().1),
        final(map).map()[rxs[res.0 as int].id()]
            == old(map).map()[rxs[res.0 as int].id()].push(res.1),
{
    // No select in std, so poll. A real deployment would use a multi-producer
    // channel or an async runtime; the proof is indifferent to which.
    loop {
        let mut k: usize = 0;
        while k < rxs.len() {
            match rxs[k].inner.try_recv() {
                Ok(m) => { return (k, m, Tracked::assume_new()); }
                Err(_) => { k = k + 1; }
            }
        }
        std::thread::yield_now();
    }
}

/// Trusted. Constructs the two endpoint handles for a channel identifier.
///
/// It takes the channel's send and receive tokens and gives them straight back,
/// which looks pointless and is not. The machine holds exactly one of each, so
/// demanding both makes this callable AT MOST ONCE per channel. Without that,
/// two calls for one identifier would each create a fresh queue, and a sender
/// built from the first call could be paired with a receiver from the second:
/// two unrelated queues that the model believes are one channel. Every proof
/// would still hold and no message would ever arrive.
///
/// Ownership rules that out rather than a run-time table of bound names. A
/// transport whose ends live in different processes has no token to pass and
/// does need the table, with binding an already-bound address failing at run
/// time; within one program this is stronger and costs no assumption.
#[verifier::external_body]
pub fn make_endpoints<M, Inv: NetInv<M>>(
    c: Ghost<ChanId>,
    Tracked(stok): Tracked<NetSM::sent<M, Inv>>,
    Tracked(rtok): Tracked<NetSM::recvd<M, Inv>>,
) -> (res: (Sender<M>, Receiver<M>, Tracked<NetSM::sent<M, Inv>>,
            Tracked<NetSM::recvd<M, Inv>>))
    requires
        stok.key() == c@,
        rtok.key() == c@,
    ensures
        res.0.id() == c@, res.1.id() == c@,
        res.2@ == stok, res.3@ == rtok,
{
    let (tx, rx) = std::sync::mpsc::channel();
    (Sender { id: c, inner: tx }, Receiver { id: c, inner: rx },
     Tracked(stok), Tracked(rtok))
}

/// Called when a spawned thread has panicked and its tokens are therefore
/// unrecoverable. Trusted, but only because it diverges: it never returns, so
/// any postcondition holds of it.
#[verifier::external_body]
pub fn abort_on_panicked_child()
    ensures false,
{ std::process::abort() }

/// An explicit interference point: other threads run here.
///
/// It takes no proof state and carries no obligation, which is the point. Facts
/// about channels this thread owns live in tokens nobody else can hold; facts
/// about other channels are persistent and cannot be retracted; and the
/// machine's invariants are global and inductive. There is nothing to
/// re-establish, so marking a yield is documentation rather than an obligation.
/// It is not trusted -- there is nothing in it to trust.
pub fn interference_point() { }

} // verus!

// ---------------------------------------------------------------------------
// Operations available to every protocol. These are verified against `NetInv`
// and are therefore written once rather than once per protocol.
// ---------------------------------------------------------------------------
verus!{

/// Receive a message and obtain the protocol's guarantee about it.
pub fn recv_learn<M, Inv: NetInv<M>>(
    r: &Receiver<M>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):  Tracked<&mut NetSM::recvd<M, Inv>>,
) -> (m: M)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == r.id(),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key() == r.id(),
        final(tok).value() == old(tok).value().push(m),
        Inv::wit_inv(r.id(), m),
{
    let (m, w) = recv::<M, Inv>(r, Tracked(inst), Tracked(tok));
    proof { inst.learn(w@.element().0, w@.element().1, w@.element().2, w.borrow()); }
    m
}

/// A receive whose precondition is that the caller already holds a witness that
/// the message is present, at the position about to be consumed. Under that
/// precondition the operation cannot block, so it is a left mover and a send
/// followed by it forms a single atomic block.
///
/// Verified rather than trusted: it is `recv` together with determinism of
/// delivery and agreement between witnesses.
pub fn recv_abs<M, Inv: DetDelivery<M>>(
    r: &Receiver<M>,
    Tracked(inst): Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(tok):  Tracked<&mut NetSM::recvd<M, Inv>>,
    Tracked(w):    Tracked<&NetSM::was_sent<M, Inv>>,
) -> (m: M)
    requires
        old(tok).instance_id() == inst.id(),
        old(tok).key() == r.id(),
        w.instance_id() == inst.id(),
        w.element().0 == r.id(),
        Inv::deliverable_at(old(tok).value(), w.element().1),
    ensures
        final(tok).instance_id() == inst.id(),
        final(tok).key() == r.id(),
        final(tok).value() == old(tok).value().push(m),
        m == w.element().2,
{
    let ghost before = old(tok).value();
    let (m, w2) = recv::<M, Inv>(r, Tracked(inst), Tracked(tok));
    proof {
        Inv::lemma_delivery_determined(before, w.element().1, w2@.element().1);
        inst.witness_agree(w.element().0, w.element().1,
                           w.element().2, w2@.element().2, w, w2.borrow());
    }
    m
}

/// Create a channel and return both endpoints with their initially empty
/// tokens. Freshness is proved from the machine's `unallocated` invariant, not
/// asserted in this specification.
pub fn mint<M, Inv: NetInv<M>>(
    fam: Ghost<nat>, j: usize,
    Tracked(inst):  Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(alloc): Tracked<&mut NetSM::next<M, Inv>>,
) -> (res: (Sender<M>, Receiver<M>, Tracked<NetSM::sent<M, Inv>>,
            Tracked<NetSM::recvd<M, Inv>>))
    requires
        old(alloc).instance_id() == inst.id(),
    ensures
        final(alloc).instance_id() == inst.id(),
        final(alloc).value() == old(alloc).value() + 1,
        res.0.id() == dyn_chan(fam@, j as int, old(alloc).value()),
        res.1.id() == res.0.id(),
        res.2@.instance_id() == inst.id(),
        res.2@.key() == res.0.id(),
        res.2@.value() == Seq::<M>::empty(),
        res.3@.instance_id() == inst.id(),
        res.3@.key() == res.0.id(),
        res.3@.value() == Seq::<M>::empty(),
{
    let ghost c = dyn_chan(fam@, j as int, alloc.value());
    let tracked s;
    let tracked r;
    proof {
        let tracked (a, b) = inst.alloc(fam@, j as int, alloc);
        s = a.get();
        r = b.get();
    }
    let (tx, rx, Tracked(s2), Tracked(r2)) =
        make_endpoints::<M, Inv>(Ghost(c), Tracked(s), Tracked(r));
    (tx, rx, Tracked(s2), Tracked(r2))
}

/// Civl's synchronised asynchronous call. Because the handler is a left mover
/// and its request has already been sent, its action may be executed at the
/// call site: the caller performs the handler's own send, using the reply
/// channel's send token, which it holds because it created the channel.
///
/// PROOF-LEVEL. This consumes the reply channel's send token, so no handler
/// running elsewhere can ever send that reply, and a program built this way
/// would block on a real queue forever. In Civl the handler does run and the
/// proof merely reorders it; here the token surgery makes the handler's send
/// impossible rather than reordered, and recovering the distinction needs the
/// reduction argument to be real rather than documentary. See `docs/plan.md`,
/// items C and D. `rpc` and `recv_abs` inherit this.
pub proof fn absorb_handler<M, Inv: NetInv<M>>(
    tracked inst: &NetSM::Instance<M, Inv>,
    tracked reply_cap: NetSM::sent<M, Inv>,
    reply: M,
) -> (tracked r: (NetSM::sent<M, Inv>, NetSM::was_sent<M, Inv>))
    requires
        reply_cap.instance_id() == inst.id(),
        Inv::gate(reply_cap.key(), reply_cap.value(), reply),
        !Inv::needs_cause(reply_cap.key(), reply),
    ensures
        r.1.instance_id() == inst.id(),
        r.1.element() == (reply_cap.key(), reply_cap.value().len(), reply),
        r.0.value() == reply_cap.value().push(reply),
{
    let tracked none = SetToken::empty(inst.id());
    let tracked (a, b) = inst.do_send(
        reply_cap.key(), reply_cap.value(), reply, Set::empty(), reply_cap, &none);
    (a.get(), b.get())
}

/// A remote call. PROOF-LEVEL: see `absorb_handler`, whose limitation this
/// inherits. The runnable calling convention is a send followed by a receive,
/// with two interference points and no atomicity claim.
///
/// The body is a left-moving send followed by a left-moving
/// abstracted receive, so it contains no interference point and is, to its
/// caller, one atomic action.
///
/// The reply capability is taken by value and consumed: a reply channel is
/// used once, and Rust's linearity is what prevents the caller and the real
/// handler both sending the reply.
pub fn rpc<M, Inv: DetDelivery<M>>(
    req_s: &Sender<M>, req_m: M,
    rsp_r: &Receiver<M>, reply: Ghost<M>,
    Tracked(inst):      Tracked<&NetSM::Instance<M, Inv>>,
    Tracked(req_tok):   Tracked<&mut NetSM::sent<M, Inv>>,
    Tracked(reply_cap): Tracked<NetSM::sent<M, Inv>>,
    Tracked(rsp_tok):   Tracked<&mut NetSM::recvd<M, Inv>>,
) -> (m: M)
    requires
        old(req_tok).instance_id() == inst.id(),
        old(req_tok).key() == req_s.id(),
        Inv::gate(req_s.id(), old(req_tok).value(), req_m),
        reply_cap.instance_id() == inst.id(),
        reply_cap.key() == rsp_r.id(),
        Inv::gate(rsp_r.id(), reply_cap.value(), reply@),
        !Inv::needs_cause(req_s.id(), req_m),
        !Inv::needs_cause(rsp_r.id(), reply@),
        old(rsp_tok).instance_id() == inst.id(),
        old(rsp_tok).key() == rsp_r.id(),
        Inv::deliverable_at(old(rsp_tok).value(), reply_cap.value().len()),
    ensures
        m == reply@,
        final(req_tok).instance_id() == inst.id(),
        final(req_tok).key() == req_s.id(),
        final(req_tok).value() == old(req_tok).value().push(req_m),
        final(rsp_tok).instance_id() == inst.id(),
        final(rsp_tok).key() == rsp_r.id(),
{
    // A left mover.
    let _w = send::<M, Inv>(req_s, req_m, Tracked(inst), Tracked(req_tok));

    // The handler runs here, consuming the reply capability.
    let tracked w2;
    proof {
        let tracked (_spent, wit) = absorb_handler::<M, Inv>(inst, reply_cap, reply@);
        w2 = wit;
    }

    // A left mover, because the witness produced above discharges its
    // precondition, so it cannot block.
    recv_abs::<M, Inv>(rsp_r, Tracked(inst), Tracked(rsp_tok), Tracked(&w2))
}

} // verus!
