// Single-decree Paxos.
//
// Proposers and acceptors, ballots, two phases. The safety property is
// AGREEMENT: no two acceptors ever accept different values at ballots that
// could both be chosen.
//
// Three design choices are worth stating before the code, because each is
// forced by the framework rather than by Paxos.
//
// BALLOTS CARRY THEIR PROPOSER. A ballot is (round, proposer), ordered
// lexicographically, so two proposers never share a ballot and the gate on a
// proposer's channels can check `b.prop == p` locally. This is why Paxos needs
// no globally monotone counter, and therefore no protocol state inside the
// network machine.
//
// A PROPOSER COMMITS BEFORE IT SENDS. Phase two broadcasts `Accept(b, v)` to
// every acceptor -- n channels carrying what must be the same value. That the
// value is the same across those channels is a cross-channel fact, which no
// gate can see. So a proposer first appends `Decided(b, v)` to a log it alone
// owns, and every `Accept` it sends must point at that entry. Uniqueness of the
// value per ballot then becomes a property of ONE channel's history, which a
// gate can enforce, and provenance carries it to the acceptors.
//
// CHANNELS ARE PADDED TO THREE INDICES. A per-pair channel would naturally be
// `chan(fam, seq![p, a])`, but every two-index name is reserved for the
// allocator (`dyn_chan`), and `boot` requires the deployment's channels to
// avoid them. Hence the trailing 0. This is a wart in the naming scheme rather
// than in Paxos.
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::tokens::SetToken;
use crate::tok::*;
use crate::proc::*;
use crate::quorum::*;

verus! {

/// How many acceptors. A quorum is any set of more than half of them.
pub uninterp spec fn n_acc() -> int;

#[verifier::external_body]
pub proof fn acc_config()
    ensures n_acc() >= 1,
{
}

/// The acceptors. `set_int_range` carries the cardinality, which is what the
/// quorum arithmetic needs.
pub open spec fn acceptors() -> Set<int> { set_int_range(0, n_acc()) }

pub proof fn lemma_acceptors()
    ensures
        acceptors().len() == n_acc(),
        forall|a: int| acceptors().contains(a) <==> 0 <= a < n_acc(),
{
    acc_config();
    lemma_int_range(0, n_acc());
}

/// A quorum: any strict majority.
pub open spec fn is_quorum(q: Set<int>) -> bool {
    q.subset_of(acceptors()) && q.len() + q.len() > n_acc()
}

// ---------------------------------------------------------------------------
// Ballots
// ---------------------------------------------------------------------------

#[derive(Structural, PartialEq, Eq, Clone, Copy)]
pub struct Ballot { pub round: u64, pub prop: u64 }

/// Lexicographic, so ballots of distinct proposers are always comparable and
/// never equal.
pub open spec fn blt(x: Ballot, y: Ballot) -> bool {
    x.round < y.round || (x.round == y.round && x.prop < y.prop)
}

pub open spec fn ble(x: Ballot, y: Ballot) -> bool { x == y || blt(x, y) }

/// The executable comparison, tied to the specification one.
pub fn ballot_lt(x: Ballot, y: Ballot) -> (r: bool)
    ensures r == blt(x, y),
{
    x.round < y.round || (x.round == y.round && x.prop < y.prop)
}

// ---------------------------------------------------------------------------
// Channels
// ---------------------------------------------------------------------------

/// Proposer `p`'s own decision log: what it committed to, before telling anyone.
pub open spec fn pdec(p: int) -> ChanId { chan(0, seq![p]) }

/// Acceptor `a`'s own log: every promise it makes and every value it accepts,
/// in order, on ONE channel it alone owns.
///
/// This is the pattern the lease lock's journal hinted at, and Paxos forces.
/// An acceptor's local protocol -- never accept below a promise, never promise
/// below a promise -- relates its promises to its accepts, which travel on
/// different channels to different proposers. A gate sees one channel, so it
/// cannot enforce that. Routing everything through one owned log turns the
/// acceptor's whole local protocol into a condition on a single history, which
/// a gate CAN enforce, and provenance carries each outgoing message back to
/// the log entry that licensed it.
pub open spec fn alog(a: int) -> ChanId { chan(5, seq![a]) }

pub open spec fn p1a(p: int, a: int) -> ChanId { chan(1, seq![p, a, 0]) }  // Prepare
pub open spec fn p1b(p: int, a: int) -> ChanId { chan(2, seq![p, a, 0]) }  // Promise
pub open spec fn p2a(p: int, a: int) -> ChanId { chan(3, seq![p, a, 0]) }  // Accept
pub open spec fn p2b(p: int, a: int) -> ChanId { chan(4, seq![p, a, 0]) }  // Accepted

#[derive(Structural, PartialEq, Eq)]
pub enum PMsg {
    Prepare(Ballot),
    /// `Promise(b, had, ab, av)`: promised `b`; if `had`, previously accepted
    /// `(ab, av)`.
    Promise(Ballot, bool, Ballot, u64),
    /// The proposer's commitment, on its own log.
    Decided(Ballot, u64),
    Accept(Ballot, u64),
    Accepted(Ballot, u64),
    /// Acceptor log entries.
    LPromise(Ballot, bool, Ballot, u64),
    LAccept(Ballot, u64),
}

/// A decision log is a run of strictly increasing ballots, all the proposer's
/// own. That is what makes the value a FUNCTION of the ballot.
pub open spec fn log_ok(p: int, h: Seq<PMsg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len()
        ==> blt(#[trigger] h[x]->Decided_0, #[trigger] h[y]->Decided_0)
}

/// "This channel is some acceptor's Accepted channel." Says it by equality
/// rather than by picking apart the name, so `wit_inv` can be instantiated.
pub open spec fn is_p2b(c: ChanId) -> bool { c == p2b(c.ix[0], c.ix[1]) }
pub open spec fn is_p2a(c: ChanId) -> bool { c == p2a(c.ix[0], c.ix[1]) }
pub open spec fn is_pdec(c: ChanId) -> bool { c == pdec(c.ix[0]) }

/// Every `Accept` ever sent is backed by the proposer's own commitment.
pub open spec fn rec_accept_backed(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_p2a(c)
            ==> exists|j: nat| ws.contains(
                    (pdec(c.ix[0]), j, PMsg::Decided(m->Accept_0, m->Accept_1)))
}

pub open spec fn is_alog(c: ChanId) -> bool { c == alog(c.ix[0]) }
pub open spec fn is_p1b(c: ChanId) -> bool { c == p1b(c.ix[0], c.ix[1]) }

/// Every promise an acceptor sent is backed by an entry in its own log.
pub open spec fn rec_promise_logged(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_p1b(c)
            ==> exists|j: nat| ws.contains((alog(c.ix[1]), j,
                    PMsg::LPromise(m->Promise_0, m->Promise_1, m->Promise_2, m->Promise_3)))
}

/// And every acceptance likewise.
pub open spec fn rec_accepted_logged(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_p2b(c)
            ==> exists|j: nat| ws.contains((alog(c.ix[1]), j,
                    PMsg::LAccept(m->Accepted_0, m->Accepted_1)))
}

/// The acceptor's ordering protocol, carried in the RECORD rather than in the
/// history.
///
/// The record stores an index with every message, so it can express order --
/// which is not obvious, and is what lets the whole Paxos argument live in one
/// domain instead of straddling `history_inv` and `record_inv`. Preserving it
/// needs the gate and the history, which `lemma_record_inv_preserved` now
/// receives.
pub open spec fn rec_alog_ok(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m1: PMsg, j: nat, m2: PMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, j, m2)))
        && is_alog(c) && i < j
            ==> {
                &&& (m1 is LPromise && m2 is LPromise
                        ==> blt(m1->LPromise_0, m2->LPromise_0))
                &&& (m1 is LPromise && m2 is LAccept
                        ==> ble(m1->LPromise_0, m2->LAccept_0))
                &&& (m1 is LAccept && m2 is LPromise
                        ==> m2->LPromise_1 && ble(m1->LAccept_0, m2->LPromise_2))
            }
}

/// A promise the acceptor sent to proposer `p`.
pub open spec fn promised(
    ws: Set<(ChanId, nat, PMsg)>, p: int, a: int, b: Ballot, had: bool, ab: Ballot, av: u64,
) -> bool {
    exists|i: nat| ws.contains((p1b(p, a), i, PMsg::Promise(b, had, ab, av)))
}

/// THE PROPOSER'S PHASE-ONE OBLIGATION.
///
/// `v` was not chosen freely: a quorum promised `b`, and `v` is the value of the
/// highest report among them -- or nobody reported anything, and `v` is free.
/// This is what a proposer must present witnesses for before it may commit.
pub open spec fn quorum_backs(
    ws: Set<(ChanId, nat, PMsg)>, p: int, b: Ballot, v: u64,
) -> bool {
    exists|q: Set<int>| is_quorum(q)
        && (forall|a: int| q.contains(a)
                ==> exists|had: bool, ab: Ballot, av: u64| promised(ws, p, a, b, had, ab, av))
        && (
            (forall|a: int, ab: Ballot, av: u64|
                !(q.contains(a) && promised(ws, p, a, b, true, ab, av)))
            || (exists|a0: int, ab0: Ballot|
                    q.contains(a0) && promised(ws, p, a0, b, true, ab0, v)
                    && forall|a: int, ab: Ballot, av: u64|
                        q.contains(a) && promised(ws, p, a, b, true, ab, av) ==> ble(ab, ab0))
          )
}

/// Every commitment is backed by such a quorum.
pub open spec fn rec_decided_backed(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_pdec(c) && m is Decided
            ==> quorum_backs(ws, c.ix[0], m->Decided_0, m->Decided_1)
}

/// A promise reports strictly below the ballot it promises. A fact about ONE
/// entry, so it cannot live in the pairwise clause -- which is where it was
/// first written, and why it was unavailable for a log with a single entry.
pub open spec fn rec_promise_strict(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_alog(c) && m is LPromise && m->LPromise_1
            ==> blt(m->LPromise_2, m->LPromise_0)
}

/// And it reports an acceptance the acceptor really made. Establishing this in
/// record-land needs the record to be COMPLETE with respect to the histories:
/// the gate saw the acceptance in the history, and completeness is what puts it
/// in the record.
pub open spec fn rec_report_logged(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_alog(c) && m is LPromise && m->LPromise_1
            ==> exists|j: nat| ws.contains(
                    (c, j, PMsg::LAccept(m->LPromise_2, m->LPromise_3)))
}

/// One position of one channel carries one message. Immediate from the
/// machine's agreement invariant, but needed in record-land where the
/// histories are not in scope.
pub open spec fn rec_functional(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m1: PMsg, m2: PMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, i, m2)))
            ==> m1 == m2
}

/// Every acceptance an acceptor logged answers an `Accept` it was sent.
pub open spec fn rec_laccept_backed(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_alog(c) && m is LAccept
            ==> exists|j: nat| ws.contains(
                    (p2a(m->LAccept_0.prop as int, c.ix[0]), j,
                     PMsg::Accept(m->LAccept_0, m->LAccept_1)))
}

/// A proposer commits at most one value per ballot. The log's strictly
/// increasing ballots are what make this true, so it is a fact about ONE
/// channel read back through the record.
pub open spec fn rec_decided_unique(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m1: PMsg, j: nat, m2: PMsg|
        (#[trigger] ws.contains((c, i, m1))) && (#[trigger] ws.contains((c, j, m2)))
        && is_pdec(c) && m1 is Decided && m2 is Decided
        && m1->Decided_0 == m2->Decided_0
            ==> m1 == m2
}

pub struct Paxos;

impl NetInv<PMsg> for Paxos {
    open spec fn gate(c: ChanId, s: Seq<PMsg>, m: PMsg) -> bool {
        &&& (forall|p: int| c == #[trigger] pdec(p) ==> {
                &&& m is Decided
                &&& m->Decided_0.prop == p
                // strictly after everything already committed
                &&& forall|x: int| 0 <= x < s.len() ==> blt(#[trigger] s[x]->Decided_0, m->Decided_0)
            })
        // The acceptor's whole local protocol, on the one history that can see
        // it. Everything the acceptor sends is licensed by an entry here.
        &&& (forall|a: int| c == #[trigger] alog(a) ==> {
                &&& (m is LPromise || m is LAccept)
                // A report must name an acceptance this acceptor really made,
                // and one strictly below the ballot being promised. That is
                // faithful: an acceptor promises `b` only when `b` exceeds
                // everything it has promised, and it never accepts below a
                // promise, so anything it has accepted is below `b`. It is also
                // what makes the safety induction decrease.
                &&& (m is LPromise && m->LPromise_1 ==> {
                        &&& blt(m->LPromise_2, m->LPromise_0)
                        &&& exists|x: int| 0 <= x < s.len()
                                && s[x] == PMsg::LAccept(m->LPromise_2, m->LPromise_3)
                    })
                &&& (m is LPromise ==> forall|x: int| 0 <= x < s.len() ==> {
                        &&& ((#[trigger] s[x]) is LPromise
                                ==> blt(s[x]->LPromise_0, m->LPromise_0))
                        &&& (s[x] is LAccept
                                ==> m->LPromise_1 && ble(s[x]->LAccept_0, m->LPromise_2))
                    })
                &&& (m is LAccept ==> forall|x: int| 0 <= x < s.len()
                        ==> ((#[trigger] s[x]) is LPromise
                                ==> ble(s[x]->LPromise_0, m->LAccept_0)))
            })
        &&& (forall|p: int, a: int| c == #[trigger] p1a(p, a)
                ==> m is Prepare && m->Prepare_0.prop == p)
        &&& (forall|p: int, a: int| c == #[trigger] p1b(p, a) ==> m is Promise)
        &&& (forall|p: int, a: int| c == #[trigger] p2a(p, a)
                ==> m is Accept && m->Accept_0.prop == p)
        &&& (forall|p: int, a: int| c == #[trigger] p2b(p, a)
                ==> m is Accepted && m->Accepted_0.prop == p)
    }

    open spec fn wit_inv(c: ChanId, m: PMsg) -> bool {
        &&& (forall|p: int| c == #[trigger] pdec(p) ==> m is Decided && m->Decided_0.prop == p)
        &&& (forall|p: int, a: int| c == #[trigger] p1a(p, a)
                ==> m is Prepare && m->Prepare_0.prop == p)
        &&& (forall|p: int, a: int| c == #[trigger] p1b(p, a) ==> m is Promise)
        &&& (forall|p: int, a: int| c == #[trigger] p2a(p, a)
                ==> m is Accept && m->Accept_0.prop == p)
        &&& (forall|p: int, a: int| c == #[trigger] p2b(p, a)
                ==> m is Accepted && m->Accepted_0.prop == p)
    }

    open spec fn deliverable_at(v: Seq<PMsg>, i: nat) -> bool { fifo_deliverable(v, i) }

    /// Every proposer's log is a strictly increasing run of its own ballots.
    ///
    /// The acceptors' logs are NOT constrained here. Their ordering discipline
    /// is stated over `was_sent` instead, in `rec_alog_ok`: the record carries
    /// positions, so it can express order, and one domain is cheaper than two.
    open spec fn history_inv(sent: Map<ChanId, Seq<PMsg>>) -> bool {
        forall|p: int| sent.dom().contains(#[trigger] pdec(p)) ==> log_ok(p, sent[pdec(p)])
    }

    /// An `Accept` must point at the proposer's own commitment; an `Accepted`
    /// must point at the `Accept` it answers.
    open spec fn needs_cause(c: ChanId, m: PMsg) -> bool {
        (is_p2a(c) && m is Accept)
            || (is_p2b(c) && m is Accepted)
            || (is_p1b(c) && m is Promise)
            || (is_alog(c) && m is LAccept)
            || (is_pdec(c) && m is Decided)
    }

    /// Each of these derives the channel it points at from `c`, so a
    /// participant cannot present somebody else's message.
    open spec fn caused_by(c: ChanId, m: PMsg, causes: Set<(ChanId, nat, PMsg)>) -> bool {
        &&& (is_p2a(c) ==> exists|j: nat| causes.contains(
                (pdec(c.ix[0]), j, PMsg::Decided(m->Accept_0, m->Accept_1))))
        // An acceptance points at the acceptor's own log entry. It does not
        // also have to point at the `Accept` it answers: the log entry already
        // does, by `rec_laccept_backed`, so the second edge is derivable.
        &&& (is_p2b(c) ==> exists|j: nat| causes.contains(
                (alog(c.ix[1]), j,
                 PMsg::LAccept(m->Accepted_0, m->Accepted_1))))
        // A commitment must present a quorum of promises. `causes` has the same
        // type as the record, so the obligation is literally the same predicate.
        &&& (is_pdec(c) && m is Decided
                ==> quorum_backs(causes, c.ix[0], m->Decided_0, m->Decided_1))
        &&& (is_alog(c) && m is LAccept ==> exists|j: nat| causes.contains(
                (p2a(m->LAccept_0.prop as int, c.ix[0]), j,
                 PMsg::Accept(m->LAccept_0, m->LAccept_1))))
        &&& (is_p1b(c) ==> exists|j: nat| causes.contains(
                (alog(c.ix[1]), j,
                 PMsg::LPromise(m->Promise_0, m->Promise_1, m->Promise_2, m->Promise_3))))
    }

    /// The per-cause form. Two of the five kinds of caused send need SEVERAL
    /// witnesses -- an acceptance answers both an Accept and its own log entry,
    /// and a commitment needs a whole quorum -- so a single cause never
    /// suffices there and this is `false`. Those use `send_general`.
    open spec fn caused_by1(c: ChanId, m: PMsg, d: ChanId, j: nat, m2: PMsg) -> bool {
        &&& (is_p2a(c) ==> d == pdec(c.ix[0])
                && m2 == PMsg::Decided(m->Accept_0, m->Accept_1))
        &&& (is_p1b(c) ==> d == alog(c.ix[1])
                && m2 == PMsg::LPromise(m->Promise_0, m->Promise_1,
                                        m->Promise_2, m->Promise_3))
        &&& (is_alog(c) && m is LAccept ==> d == p2a(m->LAccept_0.prop as int, c.ix[0])
                && m2 == PMsg::Accept(m->LAccept_0, m->LAccept_1))
        &&& (is_p2b(c) ==> d == alog(c.ix[1])
                && m2 == PMsg::LAccept(m->Accepted_0, m->Accepted_1))
        &&& !(is_pdec(c) && m is Decided)
    }

    proof fn lemma_caused_by1(c: ChanId, m: PMsg, d: ChanId, j: nat, m2: PMsg) {
        let cs = set![(d, j, m2)];
        if is_p2a(c) {
            assert(cs.contains(
                (pdec(c.ix[0]), j, PMsg::Decided(m->Accept_0, m->Accept_1))));
        }
        if is_p1b(c) {
            assert(cs.contains((alog(c.ix[1]), j,
                PMsg::LPromise(m->Promise_0, m->Promise_1,
                               m->Promise_2, m->Promise_3))));
        }
        if is_alog(c) && m is LAccept {
            assert(cs.contains((p2a(m->LAccept_0.prop as int, c.ix[0]), j,
                PMsg::Accept(m->LAccept_0, m->LAccept_1))));
        }
        if is_p2b(c) {
            assert(cs.contains((alog(c.ix[1]), j,
                PMsg::LAccept(m->Accepted_0, m->Accepted_1))));
        }
    }

    /// An acceptance answers the Accept that arrived AND is recorded in the
    /// acceptor's own log. Exactly two causes.
    open spec fn cause_gives(c: ChanId, m: PMsg) -> bool { true }

    /// No cross-position obligation on a single history. The acceptors'
    /// ordering discipline lives in `rec_alog_ok` over `was_sent`, which can
    /// state it because the record carries positions.
    open spec fn pair_gives(c: ChanId, m1: PMsg, m2: PMsg) -> bool { true }

    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<PMsg>>, c: ChanId,
                                i: nat, j: nat, m1: PMsg, m2: PMsg) { }

    proof fn lemma_gate_gives_inv(c: ChanId, s: Seq<PMsg>, m: PMsg) { }

    proof fn lemma_cause_gives(c: ChanId, m: PMsg, causes: Set<(ChanId, nat, PMsg)>) { }

    /// THE CROSS-PARTICIPANT FACT: every `Accepted` an acceptor ever sent is
    /// answering an `Accept` the proposer really sent to it.
    ///
    /// No gate can see this -- it relates two channels -- and it is provable
    /// only because the send that produced the `Accepted` had to present the
    /// witness for the `Accept`.
    ///
    /// Stated over the RECORD rather than over the histories. Over `sent` this
    /// same fact needs a map insertion and sequence indices at every step, and
    /// did not go through; here preservation concerns one element.
    open spec fn record_inv(was_sent: Set<(ChanId, nat, PMsg)>) -> bool {
        &&& rec_accept_backed(was_sent)
        &&& rec_decided_unique(was_sent)
        &&& rec_alog_ok(was_sent)
        &&& rec_promise_logged(was_sent)
        &&& rec_accepted_logged(was_sent)
        &&& rec_laccept_backed(was_sent)
        &&& rec_functional(was_sent)
        &&& rec_decided_backed(was_sent)
        &&& rec_promise_strict(was_sent)
        &&& rec_report_logged(was_sent)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, PMsg)>,
                                     sent: Map<ChanId, Seq<PMsg>>,
                                     c: ChanId, s: Seq<PMsg>, m: PMsg,
                                     causes: Set<(ChanId, nat, PMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

        // ---- every Accept is backed by the proposer's commitment ----
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_p2a(k)
            implies exists|j2: nat| post.contains(
                (pdec(k.ix[0]), j2, PMsg::Decided(mm->Accept_0, mm->Accept_1))) by {
            if (k, x, mm) == e {
                assert(mm is Accept);
                assert(c.fam == 3) by { assert(k == p2a(k.ix[0], k.ix[1])); }
                assert(Self::needs_cause(c, m));
                let j0 = choose|j2: nat| causes.contains(
                    (pdec(c.ix[0]), j2, PMsg::Decided(m->Accept_0, m->Accept_1)));
                assert(post.contains(
                    (pdec(k.ix[0]), j0, PMsg::Decided(mm->Accept_0, mm->Accept_1))));
            } else {
                let jj = choose|j2: nat| was_sent.contains(
                    (pdec(k.ix[0]), j2, PMsg::Decided(mm->Accept_0, mm->Accept_1)));
                assert(post.contains(
                    (pdec(k.ix[0]), jj, PMsg::Decided(mm->Accept_0, mm->Accept_1))));
            }
        }

        // ---- promises and acceptances are in the acceptor's own log ----
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_p1b(k)
            implies exists|j2: nat| post.contains((alog(k.ix[1]), j2,
                PMsg::LPromise(mm->Promise_0, mm->Promise_1,
                               mm->Promise_2, mm->Promise_3))) by {
            if (k, x, mm) == e {
                assert(mm is Promise);
                assert(Self::needs_cause(c, m));
                let j0 = choose|j2: nat| causes.contains((alog(c.ix[1]), j2,
                    PMsg::LPromise(m->Promise_0, m->Promise_1,
                                   m->Promise_2, m->Promise_3)));
                assert(post.contains((alog(k.ix[1]), j0,
                    PMsg::LPromise(mm->Promise_0, mm->Promise_1,
                                   mm->Promise_2, mm->Promise_3))));
            } else {
                let jj = choose|j2: nat| was_sent.contains((alog(k.ix[1]), j2,
                    PMsg::LPromise(mm->Promise_0, mm->Promise_1,
                                   mm->Promise_2, mm->Promise_3)));
                assert(post.contains((alog(k.ix[1]), jj,
                    PMsg::LPromise(mm->Promise_0, mm->Promise_1,
                                   mm->Promise_2, mm->Promise_3))));
            }
        }
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_p2b(k)
            implies exists|j2: nat| post.contains((alog(k.ix[1]), j2,
                PMsg::LAccept(mm->Accepted_0, mm->Accepted_1))) by {
            if (k, x, mm) == e {
                assert(mm is Accepted);
                assert(Self::needs_cause(c, m));
                let j0 = choose|j2: nat| causes.contains((alog(c.ix[1]), j2,
                    PMsg::LAccept(m->Accepted_0, m->Accepted_1)));
                assert(post.contains((alog(k.ix[1]), j0,
                    PMsg::LAccept(mm->Accepted_0, mm->Accepted_1))));
            } else {
                let jj = choose|j2: nat| was_sent.contains((alog(k.ix[1]), j2,
                    PMsg::LAccept(mm->Accepted_0, mm->Accepted_1)));
                assert(post.contains((alog(k.ix[1]), jj,
                    PMsg::LAccept(mm->Accepted_0, mm->Accepted_1))));
            }
        }

        // ---- a promise reports strictly below, and reports something real ----
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_alog(k)
            && mm is LPromise && mm->LPromise_1
            implies blt(mm->LPromise_2, mm->LPromise_0) by {
            if (k, x, mm) != e { }
        }
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_alog(k)
            && mm is LPromise && mm->LPromise_1
            implies exists|j2: nat| post.contains(
                (k, j2, PMsg::LAccept(mm->LPromise_2, mm->LPromise_3))) by {
            if (k, x, mm) == e {
                // The gate saw the acceptance in the history; completeness puts
                // it in the record.
                let x0 = choose|x0: int| 0 <= x0 < s.len()
                    && s[x0] == PMsg::LAccept(m->LPromise_2, m->LPromise_3);
                assert(was_sent.contains((c, x0 as nat, s[x0])));
                assert(post.contains(
                    (k, x0 as nat, PMsg::LAccept(mm->LPromise_2, mm->LPromise_3))));
            } else {
                let jj = choose|j2: nat| was_sent.contains(
                    (k, j2, PMsg::LAccept(mm->LPromise_2, mm->LPromise_3)));
                assert(post.contains(
                    (k, jj, PMsg::LAccept(mm->LPromise_2, mm->LPromise_3))));
            }
        }

        // ---- one position, one message ----
        assert forall|k: ChanId, x: nat, mm1: PMsg, mm2: PMsg|
            (#[trigger] post.contains((k, x, mm1))) && (#[trigger] post.contains((k, x, mm2)))
            implies mm1 == mm2 by {
            if (k, x, mm1) == e && (k, x, mm2) != e {
                assert(k == c && sent[c] == s && x < s.len() && s[x as int] == mm2);
            } else if (k, x, mm2) == e && (k, x, mm1) != e {
                assert(k == c && sent[c] == s && x < s.len() && s[x as int] == mm1);
            }
        }

        // ---- a logged acceptance answers an Accept ----
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_alog(k) && mm is LAccept
            implies exists|j2: nat| post.contains(
                (p2a(mm->LAccept_0.prop as int, k.ix[0]), j2,
                 PMsg::Accept(mm->LAccept_0, mm->LAccept_1))) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                let j0 = choose|j2: nat| causes.contains(
                    (p2a(m->LAccept_0.prop as int, c.ix[0]), j2,
                     PMsg::Accept(m->LAccept_0, m->LAccept_1)));
                assert(post.contains(
                    (p2a(mm->LAccept_0.prop as int, k.ix[0]), j0,
                     PMsg::Accept(mm->LAccept_0, mm->LAccept_1))));
            } else {
                let jj = choose|j2: nat| was_sent.contains(
                    (p2a(mm->LAccept_0.prop as int, k.ix[0]), j2,
                     PMsg::Accept(mm->LAccept_0, mm->LAccept_1)));
                assert(post.contains(
                    (p2a(mm->LAccept_0.prop as int, k.ix[0]), jj,
                     PMsg::Accept(mm->LAccept_0, mm->LAccept_1))));
            }
        }

        // ---- the acceptor's ordering protocol, in the record ----
        assert forall|k: ChanId, x: nat, mm1: PMsg, y: nat, mm2: PMsg|
            (#[trigger] post.contains((k, x, mm1))) && (#[trigger] post.contains((k, y, mm2)))
            && is_alog(k) && x < y
            implies {
                &&& (mm1 is LPromise && mm2 is LPromise
                        ==> blt(mm1->LPromise_0, mm2->LPromise_0))
                &&& (mm1 is LPromise && mm2 is LAccept
                        ==> ble(mm1->LPromise_0, mm2->LAccept_0))
                &&& (mm1 is LAccept && mm2 is LPromise
                        ==> mm2->LPromise_1 && ble(mm1->LAccept_0, mm2->LPromise_2))
                &&& (mm2 is LPromise && mm2->LPromise_1
                        ==> blt(mm2->LPromise_2, mm2->LPromise_0))
            } by {
            if (k, y, mm2) == e {
                // The new entry, compared against an older one on the same log.
                // The gate checked exactly this against every element of `s`,
                // and agreement says the older witness names one of them.
                assert(k == c && sent[c] == s);
                assert(x < s.len() && s[x as int] == mm1);
            } else if (k, x, mm1) == e {
                // Impossible: the new entry is at the end, so nothing is after it.
                assert(k == c && sent[c] == s);
                assert(y < s.len());
            }
        }

        // ---- every commitment is backed by a quorum of promises ----
        //
        // The obligation is not monotone for free: a promise arriving later
        // could in principle beat the highest report the proposer saw. It does
        // not, because a promise is determined by its acceptor and ballot --
        // which is what `lemma_quorum_backs_mono` needs the three clauses
        // already established above for.
        assert(rec_alog_ok(post));
        assert(rec_functional(post));
        assert(rec_promise_logged(post));
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_pdec(k) && mm is Decided
            implies quorum_backs(post, k.ix[0], mm->Decided_0, mm->Decided_1) by {
            if (k, x, mm) == e {
                assert(Self::needs_cause(c, m));
                assert(quorum_backs(causes, c.ix[0], m->Decided_0, m->Decided_1));
                lemma_quorum_backs_mono(causes, post, k.ix[0],
                                        mm->Decided_0, mm->Decided_1);
            } else {
                lemma_quorum_backs_mono(was_sent, post, k.ix[0],
                                        mm->Decided_0, mm->Decided_1);
            }
        }

        // ---- one value per ballot, per proposer ----
        //
        // The new entry cannot collide with an old one, because the gate on a
        // decision log demands a ballot strictly greater than everything there
        // -- and the agreement invariant is what turns "everything in the
        // record on this channel" into "everything in this history".
        assert forall|k: ChanId, x: nat, mm1: PMsg, y: nat, mm2: PMsg|
            (#[trigger] post.contains((k, x, mm1))) && (#[trigger] post.contains((k, y, mm2)))
            && is_pdec(k) && mm1 is Decided && mm2 is Decided
            && mm1->Decided_0 == mm2->Decided_0
            implies mm1 == mm2 by {
            if (k, x, mm1) == e && (k, y, mm2) != e {
                assert(k == c && sent[c] == s);
                assert(y < s.len() && s[y as int] == mm2);
                assert(blt(mm2->Decided_0, m->Decided_0));
            } else if (k, y, mm2) == e && (k, x, mm1) != e {
                assert(k == c && sent[c] == s);
                assert(x < s.len() && s[x as int] == mm1);
                assert(blt(mm1->Decided_0, m->Decided_0));
            }
        }
    }

    proof fn lemma_history_inv_init(chans: Set<ChanId>) { }

    proof fn lemma_history_inv_alloc(sent: Map<ChanId, Seq<PMsg>>, c: ChanId) {
        let post = sent.insert(c, Seq::<PMsg>::empty());
        assert forall|p: int| post.dom().contains(#[trigger] pdec(p))
            implies log_ok(p, post[pdec(p)]) by {
            if c != pdec(p) { assert(sent.dom().contains(pdec(p))); }
        }
    }

    proof fn lemma_history_inv_preserved(sent: Map<ChanId, Seq<PMsg>>,
                                   was_sent: Set<(ChanId, nat, PMsg)>,
                                   c: ChanId, s: Seq<PMsg>, m: PMsg,
                                   causes: Set<(ChanId, nat, PMsg)>) {
        let post = sent.insert(c, s.push(m));
        assert forall|p: int| post.dom().contains(#[trigger] pdec(p))
            implies log_ok(p, post[pdec(p)]) by {
            if c == pdec(p) {
                assert forall|x: int, y: int| 0 <= x < y < s.push(m).len()
                    implies blt(#[trigger] s.push(m)[x]->Decided_0,
                                #[trigger] s.push(m)[y]->Decided_0) by {
                    if y < s.len() { assert(blt(s[x]->Decided_0, s[y]->Decided_0)); }
                    else { assert(s.push(m)[y] == m); assert(blt(s[x]->Decided_0, m->Decided_0)); }
                }
            } else {
                assert(post[pdec(p)] == sent[pdec(p)]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// What a proposer can conclude
// ---------------------------------------------------------------------------

/// Two quorums of acceptors share a member. Instantiated here so protocol code
/// never touches the set arithmetic.
pub proof fn lemma_quorum_intersect(q1: Set<int>, q2: Set<int>)
    requires is_quorum(q1), is_quorum(q2),
    ensures  exists|a: int| q1.contains(a) && q2.contains(a),
{
    lemma_acceptors();
    lemma_quorums_intersect(acceptors(), q1, q2);
}

// ---------------------------------------------------------------------------
// Safety
// ---------------------------------------------------------------------------

/// The channel names really are what `is_p1b`, `is_p2b` and friends say they
/// are. One lemma for every three-index family, so a caller never has to pick.
pub proof fn lemma_chan_shapes(p: int, a: int)
    ensures
        is_p1b(p1b(p, a)), is_p2b(p2b(p, a)), is_p2a(p2a(p, a)), is_pdec(pdec(p)),
        p1b(p, a).ix[0] == p, p1b(p, a).ix[1] == a,
        p2b(p, a).ix[0] == p, p2b(p, a).ix[1] == a,
        p2a(p, a).ix[0] == p, p2a(p, a).ix[1] == a,
        pdec(p).ix[0] == p,
{
    assert(seq![p, a, 0][0] == p);
    assert(seq![p, a, 0][1] == a);
    assert(seq![p][0] == p);
}

pub proof fn lemma_alog_shape(a: int)
    ensures is_alog(alog(a)), alog(a).ix[0] == a,
{
    assert(seq![a][0] == a);
}

/// Distinct acceptors have distinct reply channels.
pub proof fn lemma_p1b_inj(p: int, a1: int, a2: int)
    requires p1b(p, a1) == p1b(p, a2),
    ensures  a1 == a2,
{
    assert(seq![p, a1, 0][1] == a1);
    assert(seq![p, a2, 0][1] == a2);
}

/// What acceptor `a` has in its own log.
pub open spec fn logged_accept(ws: Set<(ChanId, nat, PMsg)>, a: int, b: Ballot, v: u64) -> bool {
    exists|i: nat| ws.contains((alog(a), i, PMsg::LAccept(b, v)))
}

pub open spec fn logged_promise(
    ws: Set<(ChanId, nat, PMsg)>, a: int, b: Ballot, had: bool, ab: Ballot, av: u64,
) -> bool {
    exists|i: nat| ws.contains((alog(a), i, PMsg::LPromise(b, had, ab, av)))
}

/// THE PHASE-ONE STEP, in record-land.
///
/// An acceptor that accepted `b'` and promised `b`, with `b' < b`, must have
/// REPORTED at least `b'` in that promise. The accept has to have come first,
/// because an acceptor never accepts below a promise -- so the promise's report
/// covers it.
pub proof fn lemma_log_reports_high(
    ws: Set<(ChanId, nat, PMsg)>,
    a: int, bp: Ballot, vp: u64, b: Ballot, had: bool, ab: Ballot, av: u64,
)
    requires
        rec_alog_ok(ws), rec_functional(ws),
        logged_accept(ws, a, bp, vp),
        logged_promise(ws, a, b, had, ab, av),
        blt(bp, b),
    ensures
        had && ble(bp, ab),
{
    lemma_alog_shape(a);
    let i = choose|i: nat| ws.contains((alog(a), i, PMsg::LAccept(bp, vp)));
    let j = choose|j: nat| ws.contains((alog(a), j, PMsg::LPromise(b, had, ab, av)));
    if i == j {
        assert(PMsg::LAccept(bp, vp) == PMsg::LPromise(b, had, ab, av));
    } else if j < i {
        // The acceptor would have accepted below a ballot it had promised.
        assert(ble(b, bp));
    }
}

/// An acceptor makes at most one promise per ballot, because its promises
/// strictly increase.
pub proof fn lemma_promise_unique(
    ws: Set<(ChanId, nat, PMsg)>,
    a: int, b: Ballot, h1: bool, ab1: Ballot, av1: u64,
    h2: bool, ab2: Ballot, av2: u64,
)
    requires
        rec_alog_ok(ws), rec_functional(ws),
        logged_promise(ws, a, b, h1, ab1, av1),
        logged_promise(ws, a, b, h2, ab2, av2),
    ensures
        h1 == h2 && ab1 == ab2 && av1 == av2,
{
    lemma_alog_shape(a);
    let i = choose|i: nat| ws.contains((alog(a), i, PMsg::LPromise(b, h1, ab1, av1)));
    let j = choose|j: nat| ws.contains((alog(a), j, PMsg::LPromise(b, h2, ab2, av2)));
    if i < j {
        assert(blt(b, b));
    } else if j < i {
        assert(blt(b, b));
    } else {
        assert(PMsg::LPromise(b, h1, ab1, av1) == PMsg::LPromise(b, h2, ab2, av2));
    }
}

/// A promise message is determined by its acceptor and ballot, because the log
/// entry behind it is.
pub proof fn lemma_promised_unique(
    ws: Set<(ChanId, nat, PMsg)>, p: int, a: int, b: Ballot,
    h1: bool, ab1: Ballot, av1: u64, h2: bool, ab2: Ballot, av2: u64,
)
    requires
        rec_alog_ok(ws), rec_functional(ws), rec_promise_logged(ws),
        promised(ws, p, a, b, h1, ab1, av1),
        promised(ws, p, a, b, h2, ab2, av2),
    ensures
        h1 == h2 && ab1 == ab2 && av1 == av2,
{
    lemma_chan_shapes(p, a);
    let i1 = choose|i: nat| ws.contains((p1b(p, a), i, PMsg::Promise(b, h1, ab1, av1)));
    let i2 = choose|i: nat| ws.contains((p1b(p, a), i, PMsg::Promise(b, h2, ab2, av2)));
    let j1 = choose|j: nat| ws.contains((alog(a), j, PMsg::LPromise(b, h1, ab1, av1)));
    let j2 = choose|j: nat| ws.contains((alog(a), j, PMsg::LPromise(b, h2, ab2, av2)));
    lemma_promise_unique(ws, a, b, h1, ab1, av1, h2, ab2, av2);
}

/// The proposer's obligation survives the record growing. It is not monotone
/// for free -- a later promise could in principle beat the highest report --
/// but a promise is determined by its acceptor and ballot, so there is no
/// later promise to find.
pub proof fn lemma_quorum_backs_mono(
    ws1: Set<(ChanId, nat, PMsg)>, ws2: Set<(ChanId, nat, PMsg)>,
    p: int, b: Ballot, v: u64,
)
    requires
        quorum_backs(ws1, p, b, v),
        ws1.subset_of(ws2),
        rec_alog_ok(ws2), rec_functional(ws2), rec_promise_logged(ws2),
    ensures
        quorum_backs(ws2, p, b, v),
{
    let q = choose|q: Set<int>| is_quorum(q)
        && (forall|a: int| q.contains(a)
                ==> exists|had: bool, ab: Ballot, av: u64| promised(ws1, p, a, b, had, ab, av))
        && (
            (forall|a: int, ab: Ballot, av: u64|
                !(q.contains(a) && promised(ws1, p, a, b, true, ab, av)))
            || (exists|a0: int, ab0: Ballot|
                    q.contains(a0) && promised(ws1, p, a0, b, true, ab0, v)
                    && forall|a: int, ab: Ballot, av: u64|
                        q.contains(a) && promised(ws1, p, a, b, true, ab, av) ==> ble(ab, ab0))
          );

    assert forall|a: int| q.contains(a)
        implies exists|had: bool, ab: Ballot, av: u64| promised(ws2, p, a, b, had, ab, av) by {
        let (h, x, y) = choose|had: bool, ab: Ballot, av: u64| promised(ws1, p, a, b, had, ab, av);
        let i = choose|i: nat| ws1.contains((p1b(p, a), i, PMsg::Promise(b, h, x, y)));
        assert(ws2.contains((p1b(p, a), i, PMsg::Promise(b, h, x, y))));
        assert(promised(ws2, p, a, b, h, x, y));
    }

    // Anything the larger record says about this quorum's promises for `b`, the
    // smaller one already said.
    assert forall|a: int, ab: Ballot, av: u64|
        q.contains(a) && promised(ws2, p, a, b, true, ab, av)
        implies promised(ws1, p, a, b, true, ab, av) by {
        let (h, x, y) = choose|had: bool, ab2: Ballot, av2: u64|
            promised(ws1, p, a, b, had, ab2, av2);
        let i = choose|i: nat| ws1.contains((p1b(p, a), i, PMsg::Promise(b, h, x, y)));
        assert(ws2.contains((p1b(p, a), i, PMsg::Promise(b, h, x, y))));
        assert(promised(ws2, p, a, b, h, x, y));
        lemma_promised_unique(ws2, p, a, b, h, x, y, true, ab, av);
    }

    if !(forall|a: int, ab: Ballot, av: u64|
            !(q.contains(a) && promised(ws1, p, a, b, true, ab, av))) {
        let (a0, ab0) = choose|a0: int, ab0: Ballot|
            q.contains(a0) && promised(ws1, p, a0, b, true, ab0, v)
            && forall|a: int, ab: Ballot, av: u64|
                q.contains(a) && promised(ws1, p, a, b, true, ab, av) ==> ble(ab, ab0);
        let i0 = choose|i: nat| ws1.contains((p1b(p, a0), i, PMsg::Promise(b, true, ab0, v)));
        assert(ws2.contains((p1b(p, a0), i0, PMsg::Promise(b, true, ab0, v))));
        assert(promised(ws2, p, a0, b, true, ab0, v));
    }
}

/// Acceptor `a` accepted `(b, v)`: it said so on the channel back to `b`'s
/// proposer.
pub open spec fn accepted(ws: Set<(ChanId, nat, PMsg)>, a: int, b: Ballot, v: u64) -> bool {
    exists|i: nat| ws.contains((p2b(b.prop as int, a), i, PMsg::Accepted(b, v)))
}

/// `v` is chosen at ballot `b`: a quorum of acceptors accepted it.
pub open spec fn chosen(ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v: u64) -> bool {
    exists|q: Set<int>| is_quorum(q)
        && forall|a: int| q.contains(a) ==> accepted(ws, a, b, v)
}

/// Quorums exist. Without this the safety theorem could be vacuously true for
/// want of anything ever being chosen.
pub proof fn lemma_all_is_quorum()
    ensures is_quorum(acceptors()),
{
    acc_config();
    lemma_acceptors();
}

/// A quorum is not empty.
pub proof fn lemma_quorum_nonempty(q: Set<int>)
    requires is_quorum(q),
    ensures  exists|a: int| q.contains(a),
{
    lemma_acceptors();
    if !(exists|a: int| q.contains(a)) {
        assert(q =~= Set::<int>::empty());
    }
}

/// What a proposer has gathered so far in phase one: a set `q` of acceptors
/// that have promised `b`, witnesses for each, and the highest report seen.
pub open spec fn gathered_ok(
    cs: Set<(ChanId, nat, PMsg)>, p: int, b: Ballot, q: Set<int>,
    has_best: bool, best_bal: Ballot, best_val: u64,
) -> bool {
    &&& (forall|a: int| q.contains(a)
            ==> exists|had: bool, ab: Ballot, av: u64| promised(cs, p, a, b, had, ab, av))
    &&& (has_best ==> exists|a0: int|
            q.contains(a0) && promised(cs, p, a0, b, true, best_bal, best_val))
    &&& (forall|a: int, ab: Ballot, av: u64|
            q.contains(a) && promised(cs, p, a, b, true, ab, av)
                ==> has_best && ble(ab, best_bal))
}

/// Once the gathered set is a quorum, it discharges the proposer's phase-one
/// obligation -- provided the value taken is the highest report, or anything at
/// all if nobody reported.
pub proof fn lemma_gathered_backs(
    cs: Set<(ChanId, nat, PMsg)>, p: int, b: Ballot, q: Set<int>,
    has_best: bool, best_bal: Ballot, best_val: u64, v: u64,
)
    requires
        gathered_ok(cs, p, b, q, has_best, best_bal, best_val),
        is_quorum(q),
        has_best ==> v == best_val,
    ensures
        quorum_backs(cs, p, b, v),
{
    if has_best {
        let a0 = choose|a0: int| q.contains(a0) && promised(cs, p, a0, b, true, best_bal, v);
        assert(q.contains(a0) && promised(cs, p, a0, b, true, best_bal, v)
            && forall|a: int, ab: Ballot, av: u64|
                q.contains(a) && promised(cs, p, a, b, true, ab, av) ==> ble(ab, best_bal));
    } else {
        assert(forall|a: int, ab: Ballot, av: u64|
            !(q.contains(a) && promised(cs, p, a, b, true, ab, av)));
    }
}

/// A proposer committed `(b, v)`. The ballot names its proposer, so the log is
/// determined.
pub open spec fn decided(ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v: u64) -> bool {
    exists|i: nat| ws.contains((pdec(b.prop as int), i, PMsg::Decided(b, v)))
}

/// Anything an acceptor logged as accepted was committed by its proposer.
pub proof fn lemma_logged_accept_decided(
    ws: Set<(ChanId, nat, PMsg)>, a: int, b: Ballot, v: u64,
)
    requires Paxos::record_inv(ws), logged_accept(ws, a, b, v),
    ensures  decided(ws, b, v),
{
    lemma_alog_shape(a);
    lemma_chan_shapes(b.prop as int, a);
    let i = choose|i: nat| ws.contains((alog(a), i, PMsg::LAccept(b, v)));
    let j = choose|j: nat| ws.contains(
        (p2a(b.prop as int, a), j, PMsg::Accept(b, v)));
    let k = choose|k: nat| ws.contains(
        (pdec(b.prop as int), k, PMsg::Decided(b, v)));
}

/// And anything a quorum accepted was likewise committed.
pub proof fn lemma_accepted_decided(
    ws: Set<(ChanId, nat, PMsg)>, a: int, b: Ballot, v: u64,
)
    requires Paxos::record_inv(ws), accepted(ws, a, b, v),
    ensures  decided(ws, b, v), logged_accept(ws, a, b, v),
{
    lemma_chan_shapes(b.prop as int, a);
    let i = choose|i: nat| ws.contains(
        (p2b(b.prop as int, a), i, PMsg::Accepted(b, v)));
    let j = choose|j: nat| ws.contains((alog(a), j, PMsg::LAccept(b, v)));
    lemma_logged_accept_decided(ws, a, b, v);
}

/// Two commitments at one ballot agree.
pub proof fn lemma_one_value_per_ballot_dec(
    ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v1: u64, v2: u64,
)
    requires Paxos::record_inv(ws), decided(ws, b, v1), decided(ws, b, v2),
    ensures  v1 == v2,
{
    lemma_chan_shapes(b.prop as int, 0);
    let i1 = choose|i: nat| ws.contains((pdec(b.prop as int), i, PMsg::Decided(b, v1)));
    let i2 = choose|i: nat| ws.contains((pdec(b.prop as int), i, PMsg::Decided(b, v2)));
    assert(PMsg::Decided(b, v1) == PMsg::Decided(b, v2));
}

/// SAFETY AT A BALLOT.
///
/// If a proposer committed `(b, v)`, then no earlier ballot chose anything but
/// `v`. This is the half of Paxos that phase one exists for, and the induction
/// is on the ballot: the proposer's value came from the highest report among a
/// quorum, that report names a strictly earlier ballot, and the claim at that
/// ballot is the induction hypothesis.
pub proof fn lemma_safe_at(ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v: u64)
    requires
        Paxos::record_inv(ws),
        decided(ws, b, v),
    ensures
        forall|b2: Ballot, v2: u64| blt(b2, b) && chosen(ws, b2, v2) ==> v == v2,
    decreases b.round, b.prop,
{
    assert forall|b2: Ballot, v2: u64| blt(b2, b) && chosen(ws, b2, v2) implies v == v2 by {
        let p = b.prop as int;
        lemma_chan_shapes(p, 0);
        let di = choose|i: nat| ws.contains((pdec(p), i, PMsg::Decided(b, v)));
        assert(quorum_backs(ws, p, b, v));

        let q = choose|q: Set<int>| is_quorum(q)
            && (forall|a: int| q.contains(a)
                    ==> exists|had: bool, ab: Ballot, av: u64| promised(ws, p, a, b, had, ab, av))
            && (
                (forall|a: int, ab: Ballot, av: u64|
                    !(q.contains(a) && promised(ws, p, a, b, true, ab, av)))
                || (exists|a0: int, ab0: Ballot|
                        q.contains(a0) && promised(ws, p, a0, b, true, ab0, v)
                        && forall|a: int, ab: Ballot, av: u64|
                            q.contains(a) && promised(ws, p, a, b, true, ab, av) ==> ble(ab, ab0))
              );
        let q2 = choose|q2: Set<int>| is_quorum(q2)
            && forall|a: int| q2.contains(a) ==> accepted(ws, a, b2, v2);

        // Some acceptor is in both quorums.
        lemma_quorum_intersect(q, q2);
        let a = choose|a: int| q.contains(a) && q2.contains(a);

        // It accepted (b2, v2) and it promised b.
        lemma_accepted_decided(ws, a, b2, v2);
        let (had, ab, av) = choose|had: bool, ab: Ballot, av: u64|
            promised(ws, p, a, b, had, ab, av);
        lemma_chan_shapes(p, a);
        let pi = choose|i: nat| ws.contains((p1b(p, a), i, PMsg::Promise(b, had, ab, av)));
        let li = choose|j: nat| ws.contains((alog(a), j, PMsg::LPromise(b, had, ab, av)));

        // So its promise reported at least b2 -- in particular it reported.
        lemma_log_reports_high(ws, a, b2, v2, b, had, ab, av);
        assert(promised(ws, p, a, b, true, ab, av));

        // The proposer therefore took its value from a maximal report.
        let (a0, ab0) = choose|a0: int, ab0: Ballot|
            q.contains(a0) && promised(ws, p, a0, b, true, ab0, v)
            && forall|a3: int, ab3: Ballot, av3: u64|
                q.contains(a3) && promised(ws, p, a3, b, true, ab3, av3) ==> ble(ab3, ab0);
        assert(ble(ab, ab0));
        assert(ble(b2, ab0));

        // That report names a real acceptance, at a strictly earlier ballot.
        lemma_chan_shapes(p, a0);
        let p0 = choose|i: nat| ws.contains((p1b(p, a0), i, PMsg::Promise(b, true, ab0, v)));
        let l0 = choose|j: nat| ws.contains((alog(a0), j, PMsg::LPromise(b, true, ab0, v)));
        lemma_alog_shape(a0);
        assert(blt(ab0, b));
        let lj = choose|j: nat| ws.contains((alog(a0), j, PMsg::LAccept(ab0, v)));
        assert(logged_accept(ws, a0, ab0, v));
        lemma_logged_accept_decided(ws, a0, ab0, v);

        // Induction at that earlier ballot.
        if b2 == ab0 {
            // Same ballot: one commitment per ballot settles it.
            lemma_one_value_per_ballot_dec(ws, ab0, v, v2);
        } else {
            lemma_safe_at(ws, ab0, v);
        }
    }
}

/// ONE VALUE PER BALLOT.
///
/// Whatever two acceptors accepted at the same ballot, it was the same value.
/// The chain is three cross-participant hops, each one a witness the sender was
/// required to present: an `Accepted` answers an `Accept`, an `Accept` is backed
/// by the proposer's own commitment, and a proposer commits once per ballot
/// because its log's ballots strictly increase.
///
/// No quorum reasoning is needed here at all.
pub proof fn lemma_one_value_per_ballot(
    ws: Set<(ChanId, nat, PMsg)>,
    a1: int, a2: int, b: Ballot, v1: u64, v2: u64,
)
    requires
        Paxos::record_inv(ws),
        accepted(ws, a1, b, v1),
        accepted(ws, a2, b, v2),
    ensures
        v1 == v2,
{
    let p = b.prop as int;
    lemma_chan_shapes(p, a1);
    lemma_chan_shapes(p, a2);

    let i1 = choose|i: nat| ws.contains((p2b(p, a1), i, PMsg::Accepted(b, v1)));
    let i2 = choose|i: nat| ws.contains((p2b(p, a2), i, PMsg::Accepted(b, v2)));

    // Accepted -> Accept
    let j1 = choose|j: nat| ws.contains((p2a(p, a1), j, PMsg::Accept(b, v1)));
    let j2 = choose|j: nat| ws.contains((p2a(p, a2), j, PMsg::Accept(b, v2)));

    // Accept -> Decided, both on the SAME log, because the ballot names its
    // proposer.
    let k1 = choose|k: nat| ws.contains((pdec(p), k, PMsg::Decided(b, v1)));
    let k2 = choose|k: nat| ws.contains((pdec(p), k, PMsg::Decided(b, v2)));

    // One commitment per ballot.
    assert(PMsg::Decided(b, v1) == PMsg::Decided(b, v2));
}

/// Anything chosen was committed by its proposer.
pub proof fn lemma_chosen_decided(ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v: u64)
    requires Paxos::record_inv(ws), chosen(ws, b, v),
    ensures  decided(ws, b, v),
{
    let q = choose|q: Set<int>| is_quorum(q)
        && forall|a: int| q.contains(a) ==> accepted(ws, a, b, v);
    lemma_quorum_nonempty(q);
    let a = choose|a: int| q.contains(a);
    lemma_accepted_decided(ws, a, b, v);
}

/// AGREEMENT.
///
/// Two values chosen -- at any ballots, by any quorums -- are equal. This is
/// the safety property Paxos exists for.
pub proof fn lemma_agreement(
    ws: Set<(ChanId, nat, PMsg)>, b1: Ballot, v1: u64, b2: Ballot, v2: u64,
)
    requires
        Paxos::record_inv(ws),
        chosen(ws, b1, v1),
        chosen(ws, b2, v2),
    ensures
        v1 == v2,
{
    if b1 == b2 {
        lemma_agreement_same_ballot(ws, b1, v1, v2);
    } else if blt(b2, b1) {
        lemma_chosen_decided(ws, b1, v1);
        lemma_safe_at(ws, b1, v1);
    } else {
        lemma_chosen_decided(ws, b2, v2);
        lemma_safe_at(ws, b2, v2);
    }
}

/// AGREEMENT AT A BALLOT: two values chosen at the same ballot are equal.
pub proof fn lemma_agreement_same_ballot(
    ws: Set<(ChanId, nat, PMsg)>, b: Ballot, v1: u64, v2: u64,
)
    requires
        Paxos::record_inv(ws),
        chosen(ws, b, v1),
        chosen(ws, b, v2),
    ensures
        v1 == v2,
{
    let q1 = choose|q: Set<int>| is_quorum(q)
        && forall|a: int| q.contains(a) ==> accepted(ws, a, b, v1);
    let q2 = choose|q: Set<int>| is_quorum(q)
        && forall|a: int| q.contains(a) ==> accepted(ws, a, b, v2);
    lemma_quorum_nonempty(q1);
    lemma_quorum_nonempty(q2);
    let a1 = choose|a: int| q1.contains(a);
    let a2 = choose|a: int| q2.contains(a);
    lemma_one_value_per_ballot(ws, a1, a2, b, v1, v2);
}

// ---------------------------------------------------------------------------
// The acceptor, as running code
//
// Every gate and every provenance obligation above is discharged HERE, from
// facts about this service's own fields. That is the point of the exercise: the
// protocol's conditions turn into an ordinary state invariant on a struct.
// ---------------------------------------------------------------------------

pub struct Acceptor {
    pub id: usize,
    pub prepares:  FanIn<PMsg, Paxos>,    // p1a(p, id), one slot per proposer
    pub promises:  FanOut<PMsg, Paxos>,   // p1b(p, id)
    pub accepts:   FanIn<PMsg, Paxos>,    // p2a(p, id)
    pub accepteds: FanOut<PMsg, Paxos>,   // p2b(p, id)
    pub log:       Out<PMsg, Paxos>,      // alog(id) -- the one channel it owns alone
    /// The highest ballot promised, and the last value accepted.
    pub max_bal: Ballot,
    pub has_acc: bool,
    pub acc_bal: Ballot,
    pub acc_val: u64,
}

impl Acceptor {
    pub open spec fn np(&self) -> nat { self.prepares.len() }

    pub open spec fn inv(&self) -> bool {
        &&& self.prepares.wf() && self.promises.wf()
        &&& self.accepts.wf() && self.accepteds.wf()
        &&& self.log.wf() && self.log.id() == alog(self.id as int)
        &&& self.promises.len() == self.np() && self.accepts.len() == self.np()
        &&& self.accepteds.len() == self.np() && self.np() > 0
        &&& self.prepares.ids@  =~= Seq::new(self.np(), |p: int| p1a(p, self.id as int))
        &&& self.promises.ids@  =~= Seq::new(self.np(), |p: int| p1b(p, self.id as int))
        &&& self.accepts.ids@   =~= Seq::new(self.np(), |p: int| p2a(p, self.id as int))
        &&& self.accepteds.ids@ =~= Seq::new(self.np(), |p: int| p2b(p, self.id as int))
        &&& self.prepares.iid() == self.log.iid()
        &&& self.promises.iid() == self.log.iid()
        &&& self.accepts.iid() == self.log.iid()
        &&& self.accepteds.iid() == self.log.iid()
        // THE STATE INVARIANT. These three lines are what discharge the gate on
        // the log at every send below.
        &&& forall|x: int| 0 <= x < self.log.hist().len() ==> {
                &&& ((#[trigger] self.log.hist()[x]) is LPromise
                        ==> ble(self.log.hist()[x]->LPromise_0, self.max_bal))
                &&& (self.log.hist()[x] is LAccept
                        ==> self.has_acc && ble(self.log.hist()[x]->LAccept_0, self.acc_bal))
            }
        &&& self.has_acc ==> {
                &&& ble(self.acc_bal, self.max_bal)
                &&& exists|x: int| 0 <= x < self.log.hist().len()
                        && #[trigger] self.log.hist()[x]
                                == PMsg::LAccept(self.acc_bal, self.acc_val)
            }
    }

    /// Phase one: answer a Prepare from proposer `k`.
    pub fn handle_prepare(&mut self, k: usize)
        requires old(self).inv(), k < old(self).np(),
        ensures  final(self).inv(), final(self).np() == old(self).np(),
    {
        let m = self.prepares.recv(k);
        match m {
            PMsg::Prepare(b) => {
                if ballot_lt(self.max_bal, b) {
                    let ghost h0 = self.log.hist();
                    proof {
                        lemma_chan_shapes(k as int, self.id as int);
                        lemma_alog_shape(self.id as int);
                    }
                    // The log entry. Its gate asks four things, and all four
                    // are read straight off this struct.
                    let Tracked(wt) = self.log.send(
                        PMsg::LPromise(b, self.has_acc, self.acc_bal, self.acc_val));
                    proof {
                        // The promise points at the entry just written: same
                        // acceptor, same content.
                        assert(self.promises.id(k as int) == p1b(k as int, self.id as int));
                    }
                    // The promise itself, pointing at that entry.
                    self.promises.send_caused(k,
                        PMsg::Promise(b, self.has_acc, self.acc_bal, self.acc_val),
                        Tracked(&wt));
                    self.max_bal = b;
                    assert forall|x: int| 0 <= x < self.log.hist().len() implies {
                        &&& ((#[trigger] self.log.hist()[x]) is LPromise
                                ==> ble(self.log.hist()[x]->LPromise_0, self.max_bal))
                        &&& (self.log.hist()[x] is LAccept
                                ==> self.has_acc
                                    && ble(self.log.hist()[x]->LAccept_0, self.acc_bal))
                    } by {
                        if x < h0.len() { assert(self.log.hist()[x] == h0[x]); }
                    }
                    assert(self.has_acc ==> exists|x: int|
                        0 <= x < self.log.hist().len()
                        && #[trigger] self.log.hist()[x]
                                == PMsg::LAccept(self.acc_bal, self.acc_val)) by {
                        if self.has_acc {
                            let x0 = choose|x: int| 0 <= x < h0.len()
                                && h0[x] == PMsg::LAccept(self.acc_bal, self.acc_val);
                            assert(self.log.hist()[x0] == h0[x0]);
                        }
                    }
                }
            }
            // The request channel carries only Prepares.
            _ => { proof { assert(false); } }
        }
    }

    /// Phase two: answer an Accept from proposer `k`.
    ///
    /// Two witnesses are needed here: the `Accept` that arrived justifies the
    /// log entry, and the log entry AND the `Accept` together justify the
    /// `Accepted` sent back. That is what `send_general` is for.
    pub fn handle_accept(&mut self, k: usize)
        requires old(self).inv(), k < old(self).np(),
        ensures  final(self).inv(), final(self).np() == old(self).np(),
    {
        let (m, Tracked(w_acc)) = self.accepts.recv_wit(k);
        match m {
            PMsg::Accept(b, v) => {
                if !ballot_lt(b, self.max_bal) {
                    let ghost h0 = self.log.hist();
                    proof {
                        lemma_chan_shapes(k as int, self.id as int);
                        lemma_alog_shape(self.id as int);
                        assert(self.accepts.id(k as int) == p2a(k as int, self.id as int));
                        assert(ble(self.max_bal, b));
                        assert forall|x: int| 0 <= x < h0.len()
                            implies ((#[trigger] h0[x]) is LPromise
                                ==> ble(h0[x]->LPromise_0, b)) by {
                            if h0[x] is LPromise {
                            }
                        }
                        // The gate on this channel says the ballot names this
                        // proposer, which is what makes the cause's channel the
                        // one the witness came from.
                        assert(b.prop as int == k as int);
                        assert(self.log.id().ix[0] == self.id as int);
                    }
                    let Tracked(w_log) = self.log.send_caused(
                        PMsg::LAccept(b, v), Tracked(&w_acc));

                    proof {
                        assert(self.accepteds.id(k as int) == p2b(k as int, self.id as int));
                    }
                    self.accepteds.send_caused(k, PMsg::Accepted(b, v),
                                               Tracked(&w_log));

                    self.max_bal = b;
                    self.has_acc = true;
                    self.acc_bal = b;
                    self.acc_val = v;

                    assert forall|x: int| 0 <= x < self.log.hist().len() implies {
                        &&& ((#[trigger] self.log.hist()[x]) is LPromise
                                ==> ble(self.log.hist()[x]->LPromise_0, self.max_bal))
                        &&& (self.log.hist()[x] is LAccept
                                ==> self.has_acc
                                    && ble(self.log.hist()[x]->LAccept_0, self.acc_bal))
                    } by {
                        if x < h0.len() {
                            assert(self.log.hist()[x] == h0[x]);
                        }
                    }
                    assert(self.log.hist()[h0.len() as int] == PMsg::LAccept(b, v));
                }
            }
            _ => { proof { assert(false); } }
        }
    }
}

// ---------------------------------------------------------------------------
// The proposer, as running code
// ---------------------------------------------------------------------------

/// What a collected quorum of promises says.
///
/// `collect` hands back messages with witnesses, and a set token holding those
/// witnesses AND NOTHING ELSE. Read through `promised`, those two facts say
/// exactly: a promise is in hand for `a` if and only if `a` is one of the
/// sources, and then the report is that source's message. Everything the
/// proposer needs about the gathered set follows from this, so the fold that
/// picks the highest report is ordinary arithmetic over a vector.
pub proof fn lemma_collected_promised(
    cs: Set<(ChanId, nat, PMsg)>, p: int, b: Ballot,
    srcs: Seq<usize>, msgs: Seq<PMsg>, need: int,
)
    requires
        0 <= need, srcs.len() == need, msgs.len() == need,
        forall|i: int| 0 <= i < need
            ==> (#[trigger] msgs[i]) is Promise && msgs[i]->Promise_0 == b,
        forall|i: int| 0 <= i < need
            ==> #[trigger] promised(cs, p, srcs[i] as int, b,
                                    msgs[i]->Promise_1, msgs[i]->Promise_2,
                                    msgs[i]->Promise_3),
        forall|e: (ChanId, nat, PMsg)| cs.contains(e)
            ==> exists|i: int| 0 <= i < need
                    && e.0 == p1b(p, #[trigger] srcs[i] as int) && e.2 == msgs[i],
    ensures
        forall|a: int, had: bool, ab: Ballot, av: u64|
            #[trigger] promised(cs, p, a, b, had, ab, av)
                ==> exists|i: int| 0 <= i < need && #[trigger] srcs[i] as int == a
                        && msgs[i] == PMsg::Promise(b, had, ab, av),
{
    assert forall|a: int, had: bool, ab: Ballot, av: u64|
        #[trigger] promised(cs, p, a, b, had, ab, av) implies
        exists|i: int| 0 <= i < need && #[trigger] srcs[i] as int == a
            && msgs[i] == PMsg::Promise(b, had, ab, av) by {
        let n = choose|n: nat| cs.contains((p1b(p, a), n, PMsg::Promise(b, had, ab, av)));
        let e = (p1b(p, a), n, PMsg::Promise(b, had, ab, av));
        let i = choose|i: int| 0 <= i < need
            && e.0 == p1b(p, srcs[i] as int) && e.2 == msgs[i];
        lemma_p1b_inj(p, a, srcs[i] as int);
        assert(srcs[i] as int == a && msgs[i] == PMsg::Promise(b, had, ab, av));
    }
}

/// A proposer.
///
/// Phase one is a `collect` on the promise mailbox, so the round completes as
/// soon as a quorum has answered and does not depend on any particular
/// acceptor being alive. Nothing about the gathering survives between rounds:
/// the witnesses and the source set are locals of `gather_quorum`, handed to
/// `commit` and then dropped.
pub struct Proposer {
    pub id: usize,
    pub prepares: FanOut<PMsg, Paxos>,   // p1a(id, a)
    /// A mailbox, not a per-acceptor endpoint: phase one must take whichever
    /// promise arrives first, or a single silent acceptor stops the round.
    pub promises: Inbox<PMsg, Paxos>,    // p1b(id, a)
    pub accepts:  FanOut<PMsg, Paxos>,   // p2a(id, a)
    pub log:      Out<PMsg, Paxos>,      // pdec(id)
    pub bal: Ballot,
    pub want: u64,
}

impl Proposer {
    pub open spec fn na(&self) -> nat { self.prepares.len() }

    pub open spec fn inv(&self) -> bool {
        &&& self.prepares.wf() && self.promises.wf() && self.accepts.wf()
        &&& self.log.wf() && self.log.id() == pdec(self.id as int)
        &&& self.promises.len() == self.na() && self.accepts.len() == self.na()
        &&& self.promises.ids@ =~= Seq::new(self.na(), |a: int| p1b(self.id as int, a))
        &&& self.na() == n_acc() && self.na() > 0
        &&& self.prepares.ids@ =~= Seq::new(self.na(), |a: int| p1a(self.id as int, a))
        &&& self.accepts.ids@  =~= Seq::new(self.na(), |a: int| p2a(self.id as int, a))
        &&& self.prepares.iid() == self.log.iid()
        &&& self.promises.iid() == self.log.iid()
        &&& self.accepts.iid() == self.log.iid()
        &&& self.bal.prop == self.id
        // The commitments already made are all below the ballot in play, which
        // is what the gate on the decision log asks.
        &&& forall|x: int| 0 <= x < self.log.hist().len()
                ==> (#[trigger] self.log.hist()[x]) is Decided
                    && blt(self.log.hist()[x]->Decided_0, self.bal)
    }

    /// Phase 1a: ask every acceptor. All sends, so no interference point.
    pub fn broadcast_prepare(&mut self)
        requires old(self).inv(),
        ensures
            final(self).inv(), final(self).na() == old(self).na(),
            final(self).bal == old(self).bal,
    {
        let mut i: usize = 0;
        while i < self.prepares.count()
            invariant 0 <= i <= self.na(), self.inv(),
            decreases self.na() - i,
        {
            self.prepares.send(i, PMsg::Prepare(self.bal));
            i = i + 1;
        }
    }

    /// Phase 1b: wait for a quorum of promises and pick the value to propose.
    ///
    /// The interference point is inside `collect`. Everything after it is
    /// arithmetic on a vector the proposer owns: which report is highest.
    /// The returned witnesses discharge phase one for the returned value.
    pub fn gather_quorum(&mut self)
        -> (res: (u64, Tracked<SetToken<(ChanId, nat, PMsg), NetSM::was_sent<PMsg, Paxos>>>))
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).na() == old(self).na(),
            final(self).bal == old(self).bal,
            final(self).log.hist() == old(self).log.hist(),
            res.1@.instance_id() == final(self).log.iid(),
            quorum_backs(res.1@.set(), final(self).id as int, final(self).bal, res.0),
    {
        let b = self.bal;
        let ghost pid = self.id as int;
        proof { lemma_acceptors(); }

        // A quorum is a strict majority, and phase one takes the first one.
        let need = self.promises.count() / 2 + 1;
        assert(need + need > n_acc()) by { assert(self.na() / 2 + self.na() / 2 >= self.na() - 1); }

        let accept = |k: usize, m: &PMsg| -> (r: bool)
            ensures r == (*m is Promise && m->Promise_0 == b)
        {
            match m { PMsg::Promise(bb, _, _, _) => *bb == b, _ => false }
        };
        let ghost pspec = |k: int, m: PMsg| m is Promise && m->Promise_0 == b;
        let (srcs, msgs, Tracked(cs)) =
            self.promises.collect(need, Ghost(pspec), accept);

        // Restate what came back in the protocol's own names.
        proof {
            assert forall|i: int| 0 <= i < need as int implies
                (#[trigger] msgs@[i]) is Promise && msgs@[i]->Promise_0 == b by {
                assert(pspec(srcs@[i] as int, msgs@[i]));
            }
            assert forall|i: int| 0 <= i < need as int implies
                #[trigger] promised(cs.set(), pid, srcs@[i] as int, b,
                                    msgs@[i]->Promise_1, msgs@[i]->Promise_2,
                                    msgs@[i]->Promise_3) by {
                assert(pspec(srcs@[i] as int, msgs@[i]));
                let n = choose|n: nat| cs.set().contains(
                    (self.promises.id(srcs@[i] as int), n, msgs@[i]));
                assert(msgs@[i] == PMsg::Promise(b, msgs@[i]->Promise_1,
                                                 msgs@[i]->Promise_2, msgs@[i]->Promise_3));
                assert(cs.set().contains(
                    (p1b(pid, srcs@[i] as int), n,
                     PMsg::Promise(b, msgs@[i]->Promise_1, msgs@[i]->Promise_2,
                                   msgs@[i]->Promise_3))));
            }
            assert forall|e: (ChanId, nat, PMsg)| cs.set().contains(e) implies
                exists|i: int| 0 <= i < need as int
                    && e.0 == p1b(pid, #[trigger] srcs@[i] as int) && e.2 == msgs@[i] by {
                let i = choose|i: int| 0 <= i < need as int
                    && e.0 == self.promises.id(srcs@[i] as int) && e.2 == msgs@[i];
            }
            lemma_collected_promised(cs.set(), pid, b, srcs@, msgs@, need as int);
        }

        // Fold: the highest report among the quorum wins.
        let mut has_best = false;
        let mut best_bal = Ballot { round: 0, prop: 0 };
        let mut best_val: u64 = 0;
        let ghost mut q: Set<int> = Set::empty();
        let mut i: usize = 0;
        while i < need
            invariant
                0 <= i <= need, need <= self.na(), srcs.len() == need, msgs.len() == need,
                forall|j: int| 0 <= j < need ==> #[trigger] srcs@[j] < self.na(),
                forall|j: int, l: int| 0 <= j < need && 0 <= l < need && j != l
                    ==> #[trigger] srcs@[j] != #[trigger] srcs@[l],
                forall|j: int| 0 <= j < need
                    ==> (#[trigger] msgs@[j]) is Promise && msgs@[j]->Promise_0 == b,
                q.len() == i,
                forall|j: int| 0 <= j < i ==> q.contains(#[trigger] srcs@[j] as int),
                forall|a: int| q.contains(a)
                    ==> exists|j: int| 0 <= j < i && #[trigger] srcs@[j] as int == a,
                has_best ==> exists|j: int| 0 <= j < i
                    && #[trigger] msgs@[j] == PMsg::Promise(b, true, best_bal, best_val),
                forall|j: int| 0 <= j < i && (#[trigger] msgs@[j])->Promise_1
                    ==> has_best && ble(msgs@[j]->Promise_2, best_bal),
            decreases need - i,
        {
            let ghost q0 = q;
            let ghost hb0 = has_best;
            let ghost bb0 = best_bal;
            let ghost bv0 = best_val;
            match &msgs[i] {
                PMsg::Promise(_, had, ab, av) => {
                    if *had && (!has_best || ballot_lt(best_bal, *ab)) {
                        has_best = true;
                        best_bal = *ab;
                        best_val = *av;
                    }
                }
                _ => { proof { assert(false); } }
            }
            proof {
                q = q.insert(srcs@[i as int] as int);
                assert(!q0.contains(srcs@[i as int] as int));
                assert forall|j: int| 0 <= j < i + 1
                    && (#[trigger] msgs@[j])->Promise_1
                    implies has_best && ble(msgs@[j]->Promise_2, best_bal) by {
                    
                }
                assert forall|a: int| q.contains(a) implies
                    exists|j: int| 0 <= j < i + 1 && #[trigger] srcs@[j] as int == a by {
                    if a != srcs@[i as int] as int {
                        let j = choose|j: int| 0 <= j < i as int && srcs@[j] as int == a;
                        assert(0 <= j < i + 1 && srcs@[j] as int == a);
                    } else {
                        assert((i as int) < i + 1 && srcs@[i as int] as int == a);
                    }
                }
            }
            i = i + 1;
        }

        let v = if has_best { best_val } else { self.want };
        proof {
            assert(is_quorum(q)) by {
                assert forall|a: int| q.contains(a) implies acceptors().contains(a) by {
                    let j = choose|j: int| 0 <= j < need as int && srcs@[j] as int == a;
                    assert(srcs@[j] < self.na());
                }
            }
            assert(gathered_ok(cs.set(), pid, b, q, has_best, best_bal, best_val)) by {
                assert forall|a: int| q.contains(a) implies
                    exists|had: bool, ab: Ballot, av: u64|
                        promised(cs.set(), pid, a, b, had, ab, av) by {
                    let j = choose|j: int| 0 <= j < need as int && srcs@[j] as int == a;
                    assert(promised(cs.set(), pid, srcs@[j] as int, b,
                                    msgs@[j]->Promise_1, msgs@[j]->Promise_2,
                                    msgs@[j]->Promise_3));
                }
                if has_best {
                    let j = choose|j: int| 0 <= j < need as int
                        && msgs@[j] == PMsg::Promise(b, true, best_bal, best_val);
                    assert(promised(cs.set(), pid, srcs@[j] as int, b,
                                    msgs@[j]->Promise_1, msgs@[j]->Promise_2,
                                    msgs@[j]->Promise_3));
                    assert(q.contains(srcs@[j] as int)
                        && promised(cs.set(), pid, srcs@[j] as int, b, true,
                                    best_bal, best_val));
                }
                assert forall|a: int, ab: Ballot, av: u64|
                    q.contains(a) && promised(cs.set(), pid, a, b, true, ab, av)
                    implies has_best && ble(ab, best_bal) by {
                    let j = choose|j: int| 0 <= j < need as int && srcs@[j] as int == a
                        && msgs@[j] == PMsg::Promise(b, true, ab, av);
                    assert(msgs@[j]->Promise_1);
                }
            }
            lemma_gathered_backs(cs.set(), pid, b, q, has_best, best_bal, best_val, v);
        }
        (v, Tracked(cs))
    }

    /// Phase two: commit a value and tell every acceptor.
    ///
    /// The commitment's justification is the whole gathered set, which is why
    /// this is the one send in the development that genuinely needs
    /// `send_general` rather than one of the fixed-arity forms.
    ///
    /// Committing ends the round: the ballot advances, so a proposer that wants
    /// to propose again starts phase one over.
    pub fn commit(
        &mut self,
        v: u64,
        Tracked(cs): Tracked<SetToken<(ChanId, nat, PMsg), NetSM::was_sent<PMsg, Paxos>>>,
    )
        requires
            old(self).inv(),
            cs.instance_id() == old(self).log.iid(),
            quorum_backs(cs.set(), old(self).id as int, old(self).bal, v),
            old(self).bal.round < u64::MAX,
        ensures
            final(self).inv(), final(self).na() == old(self).na(),
            final(self).bal.round == old(self).bal.round + 1,
    {
        proof {
            assert(self.log.id().ix[0] == self.id as int) by {
                assert(seq![self.id as int][0] == self.id as int);
            }
        }
        let ghost h0 = self.log.hist();
        let Tracked(wd) = self.log.send_general(PMsg::Decided(self.bal, v), Tracked(&cs));

        // Tell every acceptor, each Accept pointing at the commitment.
        let mut i: usize = 0;
        while i < self.accepts.count()
            invariant
                0 <= i <= self.na(),
                self.accepts.wf(), self.accepts.len() == self.na(),
                self.accepts.ids@ =~= Seq::new(self.na(), |a: int| p2a(self.id as int, a)),
                self.accepts.iid() == self.log.iid(),
                self.bal.prop == self.id,
                wd.instance_id() == self.log.iid(),
                wd.element() == (pdec(self.id as int), h0.len(),
                                 PMsg::Decided(self.bal, v)),
            decreases self.na() - i,
        {
            proof { lemma_chan_shapes(self.id as int, i as int); }
            self.accepts.send_caused(i, PMsg::Accept(self.bal, v), Tracked(&wd));
            i = i + 1;
        }

        // Start the next round.
        let old_bal = self.bal;
        self.bal = Ballot { round: old_bal.round + 1, prop: self.id as u64 };
        assert forall|x: int| 0 <= x < self.log.hist().len()
            implies (#[trigger] self.log.hist()[x]) is Decided
                && blt(self.log.hist()[x]->Decided_0, self.bal) by {
            if x < h0.len() {
                assert(self.log.hist()[x] == h0[x]);
                assert(blt(h0[x]->Decided_0, old_bal));
            } else {
                assert(self.log.hist()[x] == PMsg::Decided(old_bal, v));
            }
        }
    }

    /// One full round: ask, gather a quorum, commit. The value committed is
    /// the proposer's own `want` only if phase one left it free.
    pub fn round(&mut self) -> (v: u64)
        requires old(self).inv(), old(self).bal.round < u64::MAX,
        ensures
            final(self).inv(), final(self).na() == old(self).na(),
            final(self).bal.round == old(self).bal.round + 1,
    {
        self.broadcast_prepare();
        let (v, Tracked(cs)) = self.gather_quorum();
        self.commit(v, Tracked(cs));
        v
    }
}

// ---------------------------------------------------------------------------
// WHAT IS PROVED
//
// AGREEMENT: `lemma_agreement`. Two values chosen -- at any ballots, by any
// quorums -- are equal. That is the safety property Paxos exists for.
//
// The argument runs entirely in RECORD-land: every fact is about `was_sent`,
// the monotone record of what was ever sent, rather than about the histories.
// That was the decision that made it tractable. The record carries an index
// with every message, so it can express order as well as existence, and its
// invariants need only be preserved against one new element at a time.
//
// The chain, from the bottom:
//
//   * an acceptor's log is its whole local protocol on one owned channel:
//     promises increase, it never accepts below a promise, and a promise
//     reports the highest ballot it has accepted, strictly below the one it
//     promises;
//   * every message a participant sends points back at the entry that
//     licensed it -- Accepted at Accept and at its own log, Accept at the
//     proposer's commitment, Promise at its own log;
//   * a commitment points at a QUORUM of promises, with the value taken from
//     the highest report among them;
//   * two majorities of a finite set intersect, so the acceptor that carries
//     an earlier chosen value into the new proposer's view always exists;
//   * and the induction on ballots closes it, the report naming a strictly
//     earlier ballot at which the claim is the induction hypothesis.
//
// Each of the four essential ingredients was checked by breaking it: letting a
// proposer pick any value, letting quorums be any set, letting a promise
// under-report, and letting an acceptor accept below a promise. All four fail
// to verify. `lemma_all_is_quorum` rules out the remaining way the theorem
// could be hollow, which is quorums being impossible.
//
// THE ACCEPTOR IS RUNNING CODE. `handle_prepare` and `handle_accept` are
// ordinary executable methods, and between them they discharge every gate and
// every provenance obligation the protocol above imposes on an acceptor --
// entirely from facts about the service's own fields. The protocol's conditions
// became a state invariant on a struct, which is the outcome the whole design
// was aiming at.
//
// Two proof-engineering lessons came out of it, both about matching the
// SYNTACTIC FORM of a definition rather than its meaning:
//
//   * state an existential using the same projections the definition uses
//     (`mm->Promise_0`), not the constructor arguments it was built from;
//   * bind the tuple you are claiming membership for to a name first, then
//     assert `contains` of that name, then the existential.
//
// Without both, every conjunct of `caused_by` proves individually and the
// conjunction does not. That is worth knowing before writing the next service.
//
// THE PROPOSER IS RUNNING CODE TOO. `gather_quorum` waits on the promise
// mailbox until a quorum of distinct acceptors has answered, folds over what
// came back to find the highest report, and hands the witnesses to `commit`.
// The gathering does not survive between rounds: it is local to the method,
// which is why `Proposer`'s invariant says nothing about it.

} // verus!
