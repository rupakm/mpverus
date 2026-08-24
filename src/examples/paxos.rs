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

/// The acceptors, built by recursion because `Set::new` is partial here (sets
/// are finite in this vstd, so it returns an `Option`). Defining it this way
/// also gives the cardinality, which the quorum arithmetic needs.
pub open spec fn acceptors_upto(k: int) -> Set<int>
    decreases k
{
    if k <= 0 { Set::empty() } else { acceptors_upto(k - 1).insert(k - 1) }
}

pub open spec fn acceptors() -> Set<int> { acceptors_upto(n_acc()) }

pub proof fn lemma_acceptors_upto(k: int)
    requires k >= 0,
    ensures
        acceptors_upto(k).finite(),
        acceptors_upto(k).len() == k,
        forall|a: int| acceptors_upto(k).contains(a) <==> 0 <= a < k,
    decreases k,
{
    if k > 0 {
        lemma_acceptors_upto(k - 1);
        assert(!acceptors_upto(k - 1).contains(k - 1));
    }
}

pub proof fn lemma_acceptors()
    ensures
        acceptors().finite(),
        acceptors().len() == n_acc(),
        forall|a: int| acceptors().contains(a) <==> 0 <= a < n_acc(),
{
    acc_config();
    lemma_acceptors_upto(n_acc());
}

/// A quorum: any strict majority.
pub open spec fn is_quorum(q: Set<int>) -> bool {
    q.subset_of(acceptors()) && q.len() + q.len() > n_acc()
}

// ---------------------------------------------------------------------------
// Ballots
// ---------------------------------------------------------------------------

#[derive(Structural, PartialEq, Eq)]
pub struct Ballot { pub round: u64, pub prop: u64 }

/// Lexicographic, so ballots of distinct proposers are always comparable and
/// never equal.
pub open spec fn blt(x: Ballot, y: Ballot) -> bool {
    x.round < y.round || (x.round == y.round && x.prop < y.prop)
}

pub open spec fn ble(x: Ballot, y: Ballot) -> bool { x == y || blt(x, y) }

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

/// The ballot an acceptor-log entry is about.
pub open spec fn entry_ballot(m: PMsg) -> Ballot {
    if m is LPromise { m->LPromise_0 } else { m->LAccept_0 }
}

/// An acceptor's local protocol, as a condition on its own log.
///
///   * promises increase;
///   * it never accepts below a ballot it has promised;
///   * a promise reports the highest ballot it has accepted so far.
///
/// All three are about ONE history, which is the point of the log.
pub open spec fn alog_ok(h: Seq<PMsg>) -> bool {
    forall|x: int, y: int| 0 <= x < y < h.len() ==> {
        &&& ((#[trigger] h[x]) is LPromise && (#[trigger] h[y]) is LPromise
                ==> blt(h[x]->LPromise_0, h[y]->LPromise_0))
        // never accept below an earlier promise
        &&& (h[x] is LPromise && h[y] is LAccept
                ==> ble(h[x]->LPromise_0, h[y]->LAccept_0))
        // a promise reports at least as high as anything accepted before it
        &&& (h[x] is LAccept && h[y] is LPromise
                ==> h[y]->LPromise_1 && ble(h[x]->LAccept_0, h[y]->LPromise_2))
    }
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

/// Every `Accepted` ever sent answers an `Accept` the proposer really sent.
pub open spec fn rec_accepted_backed(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_p2b(c)
            ==> exists|j: nat| ws.contains(
                    (p2a(c.ix[0], c.ix[1]), j,
                     PMsg::Accept(m->Accepted_0, m->Accepted_1)))
}

/// Every `Accept` ever sent is backed by the proposer's own commitment.
pub open spec fn rec_accept_backed(ws: Set<(ChanId, nat, PMsg)>) -> bool {
    forall|c: ChanId, i: nat, m: PMsg|
        (#[trigger] ws.contains((c, i, m))) && is_p2a(c)
            ==> exists|j: nat| ws.contains(
                    (pdec(c.ix[0]), j, PMsg::Decided(m->Accept_0, m->Accept_1)))
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
    open spec fn history_inv(sent: Map<ChanId, Seq<PMsg>>) -> bool {
        &&& forall|p: int| sent.dom().contains(#[trigger] pdec(p)) ==> log_ok(p, sent[pdec(p)])
        &&& forall|a: int| sent.dom().contains(#[trigger] alog(a)) ==> alog_ok(sent[alog(a)])
    }

    /// An `Accept` must point at the proposer's own commitment; an `Accepted`
    /// must point at the `Accept` it answers.
    open spec fn needs_cause(c: ChanId, m: PMsg) -> bool {
        (c.fam == 3 && m is Accept) || (c.fam == 4 && m is Accepted)
    }

    open spec fn caused_by(c: ChanId, m: PMsg, causes: Set<(ChanId, nat, PMsg)>) -> bool {
        if c.fam == 3 {
            // Accept on p2a(p, a) points at Decided on the proposer's own log.
            exists|j: nat| causes.contains(
                (pdec(c.ix[0]), j, PMsg::Decided(m->Accept_0, m->Accept_1)))
        } else {
            // Accepted on p2b(p, a) points at the Accept that arrived.
            exists|j: nat| causes.contains(
                (p2a(c.ix[0], c.ix[1]), j, PMsg::Accept(m->Accepted_0, m->Accepted_1)))
        }
    }

    open spec fn cause_gives(c: ChanId, m: PMsg) -> bool { true }

    /// THE HEART OF PAXOS, in the form a reader can use.
    ///
    /// Given two entries of one acceptor's log, `m1` before `m2`, this is what
    /// follows -- and it is pure in the two messages, so it survives being read
    /// back out of a history nobody owns.
    ///
    /// The third clause is the one the whole protocol turns on: an acceptor
    /// that accepted `b'` and later promised `b` must have REPORTED at least
    /// `b'` in that promise. A proposer that gathers a quorum of promises and
    /// takes the highest report therefore cannot miss a value that was already
    /// chosen.
    open spec fn pair_gives(c: ChanId, m1: PMsg, m2: PMsg) -> bool {
        forall|a: int| c == #[trigger] alog(a) ==> {
            &&& (m1 is LPromise && m2 is LPromise
                    ==> blt(m1->LPromise_0, m2->LPromise_0))
            &&& (m1 is LPromise && m2 is LAccept
                    ==> ble(m1->LPromise_0, m2->LAccept_0))
            &&& (m1 is LAccept && m2 is LPromise
                    ==> m2->LPromise_1 && ble(m1->LAccept_0, m2->LPromise_2))
        }
    }

    proof fn lemma_pair_gives(sent: Map<ChanId, Seq<PMsg>>, c: ChanId,
                                i: nat, j: nat, m1: PMsg, m2: PMsg) {
        assert forall|a: int| c == #[trigger] alog(a) implies {
            &&& (m1 is LPromise && m2 is LPromise
                    ==> blt(m1->LPromise_0, m2->LPromise_0))
            &&& (m1 is LPromise && m2 is LAccept
                    ==> ble(m1->LPromise_0, m2->LAccept_0))
            &&& (m1 is LAccept && m2 is LPromise
                    ==> m2->LPromise_1 && ble(m1->LAccept_0, m2->LPromise_2))
        } by {
            assert(alog_ok(sent[alog(a)]));
            assert(sent[alog(a)][i as int] == m1);
            assert(sent[alog(a)][j as int] == m2);
        }
    }

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
        &&& rec_accepted_backed(was_sent)
        &&& rec_accept_backed(was_sent)
        &&& rec_decided_unique(was_sent)
    }

    proof fn lemma_record_inv_init() { }

    proof fn lemma_record_inv_preserved(was_sent: Set<(ChanId, nat, PMsg)>,
                                     sent: Map<ChanId, Seq<PMsg>>,
                                     c: ChanId, s: Seq<PMsg>, m: PMsg,
                                     causes: Set<(ChanId, nat, PMsg)>) {
        let e = (c, s.len(), m);
        let post = was_sent.insert(e);

        // ---- every Accepted answers an Accept ----
        assert forall|k: ChanId, x: nat, mm: PMsg|
            (#[trigger] post.contains((k, x, mm))) && is_p2b(k)
            implies exists|j2: nat| post.contains(
                (p2a(k.ix[0], k.ix[1]), j2, PMsg::Accept(mm->Accepted_0, mm->Accepted_1))) by {
            if (k, x, mm) == e {
                assert(mm is Accepted);
                assert(c.fam == 4) by { assert(k == p2b(k.ix[0], k.ix[1])); }
                assert(Self::needs_cause(c, m));
                let j0 = choose|j2: nat| causes.contains(
                    (p2a(c.ix[0], c.ix[1]), j2, PMsg::Accept(m->Accepted_0, m->Accepted_1)));
                assert(post.contains(
                    (p2a(k.ix[0], k.ix[1]), j0, PMsg::Accept(mm->Accepted_0, mm->Accepted_1))));
            } else {
                let jj = choose|j2: nat| was_sent.contains(
                    (p2a(k.ix[0], k.ix[1]), j2, PMsg::Accept(mm->Accepted_0, mm->Accepted_1)));
                assert(post.contains(
                    (p2a(k.ix[0], k.ix[1]), jj, PMsg::Accept(mm->Accepted_0, mm->Accepted_1))));
            }
        }

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
        assert forall|a: int| post.dom().contains(#[trigger] alog(a))
            implies alog_ok(post[alog(a)]) by {
            if c != alog(a) { assert(sent.dom().contains(alog(a))); }
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
        assert forall|a: int| post.dom().contains(#[trigger] alog(a))
            implies alog_ok(post[alog(a)]) by {
            if c == alog(a) {
                assert forall|x: int, y: int| 0 <= x < y < s.push(m).len() implies {
                    &&& ((#[trigger] s.push(m)[x]) is LPromise && (#[trigger] s.push(m)[y]) is LPromise
                            ==> blt(s.push(m)[x]->LPromise_0, s.push(m)[y]->LPromise_0))
                    &&& (s.push(m)[x] is LPromise && s.push(m)[y] is LAccept
                            ==> ble(s.push(m)[x]->LPromise_0, s.push(m)[y]->LAccept_0))
                    &&& (s.push(m)[x] is LAccept && s.push(m)[y] is LPromise
                            ==> s.push(m)[y]->LPromise_1
                                && ble(s.push(m)[x]->LAccept_0, s.push(m)[y]->LPromise_2))
                } by {
                    if y < s.len() {
                        assert(s.push(m)[x] == s[x] && s.push(m)[y] == s[y]);
                    } else {
                        assert(s.push(m)[x] == s[x] && s.push(m)[y] == m);
                    }
                }
            } else {
                assert(post[alog(a)] == sent[alog(a)]);
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

/// THE PROPOSER'S KEY STEP, from two witnesses on one acceptor's log.
///
/// If acceptor `a` accepted `(bp, vp)` and LATER promised `b`, then the promise
/// reported a ballot at least `bp`. So a proposer that takes the highest report
/// across a quorum of promises cannot be behind a value that was already
/// accepted by a member of that quorum.
///
/// Nothing here owns `alog(a)`; the fact comes back out through `learn_pair`,
/// projected to a predicate about the two messages alone.
pub proof fn lemma_promise_reports_high(
    tracked inst: &NetSM::Instance<PMsg, Paxos>,
    tracked w_acc: &NetSM::was_sent<PMsg, Paxos>,
    tracked w_pro: &NetSM::was_sent<PMsg, Paxos>,
    a: int, i: nat, j: nat,
    bp: Ballot, vp: u64, b: Ballot, had: bool, ab: Ballot, av: u64,
)
    requires
        w_acc.instance_id() == inst.id(),
        w_acc.element() == (alog(a), i, PMsg::LAccept(bp, vp)),
        w_pro.instance_id() == inst.id(),
        w_pro.element() == (alog(a), j, PMsg::LPromise(b, had, ab, av)),
        i < j,
    ensures
        had && ble(bp, ab),
{
    inst.learn_pair(alog(a), i, j,
                    PMsg::LAccept(bp, vp), PMsg::LPromise(b, had, ab, av),
                    w_acc, w_pro);
}

/// The other order is not a gap but a contradiction in waiting: an acceptor
/// that promised `b` and only afterwards accepted `bp` cannot have `bp < b`.
pub proof fn lemma_accept_after_promise(
    tracked inst: &NetSM::Instance<PMsg, Paxos>,
    tracked w_pro: &NetSM::was_sent<PMsg, Paxos>,
    tracked w_acc: &NetSM::was_sent<PMsg, Paxos>,
    a: int, i: nat, j: nat,
    b: Ballot, had: bool, ab: Ballot, av: u64, bp: Ballot, vp: u64,
)
    requires
        w_pro.instance_id() == inst.id(),
        w_pro.element() == (alog(a), i, PMsg::LPromise(b, had, ab, av)),
        w_acc.instance_id() == inst.id(),
        w_acc.element() == (alog(a), j, PMsg::LAccept(bp, vp)),
        i < j,
    ensures
        ble(b, bp),
{
    inst.learn_pair(alog(a), i, j,
                    PMsg::LPromise(b, had, ab, av), PMsg::LAccept(bp, vp),
                    w_pro, w_acc);
}

// ---------------------------------------------------------------------------
// Safety
// ---------------------------------------------------------------------------

/// The channel names really are what `is_p2b` and friends say they are.
pub proof fn lemma_chan_shapes(p: int, a: int)
    ensures
        is_p2b(p2b(p, a)), is_p2a(p2a(p, a)), is_pdec(pdec(p)),
        p2b(p, a).ix[0] == p, p2b(p, a).ix[1] == a,
        p2a(p, a).ix[0] == p, p2a(p, a).ix[1] == a,
        pdec(p).ix[0] == p,
{
    assert(seq![p, a, 0][0] == p);
    assert(seq![p, a, 0][1] == a);
    assert(seq![p][0] == p);
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
// WHAT IS AND IS NOT PROVED
//
// PROVED: agreement at a ballot. Two values chosen at the same ballot are
// equal, and more strongly, whatever any two acceptors accepted at one ballot
// was the same value. That runs a chain of three cross-participant hops --
// Accepted answers Accept, Accept is backed by the proposer's commitment, a
// proposer commits once per ballot -- each licensed by a witness the sender was
// required to present. It needs no quorum reasoning at all.
//
// PROVED, and waiting to be used: the acceptor's local protocol, its export as
// a pure pairwise fact (`lemma_promise_reports_high`), and quorum intersection
// (`lemma_quorum_intersect`). Those are the two halves of the phase-one
// argument.
//
// NOT PROVED: agreement ACROSS ballots -- that a value chosen at `b` is the
// only value any later ballot can choose. This is the half of Paxos that phase
// one exists for, and it needs two things this file does not yet have.
//
//   1. `Decided(b, v)` must be justified by a QUORUM of promises for `b`, with
//      `v` the value of the highest report among them. The framework admits
//      this -- `caused_by` takes a set of causes precisely so that a quorum can
//      justify a message -- but the gate and the causes are not written.
//
//   2. An induction over ballots. The proposer's value came from the highest
//      reported ballot `bm < b`, and concluding it agrees with a value chosen
//      at `b' <= bm` is the induction hypothesis at `bm`. Verus can carry this
//      with `decreases b.round, b.prop`, but it has not been attempted.
//
// Neither is a limitation of the framework; both are proof work.

} // verus!
