#![allow(unused_imports)]
use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

verus!{ pub type ChanId = nat; }

tokenized_state_machine!{
    FifoSM<M> {
        fields {
            #[sharding(map)]
            pub sent: Map<ChanId, Seq<M>>,
            #[sharding(map)]
            pub recvd: Map<ChanId, Seq<M>>,
        }

        transition!{
            do_send(c: ChanId, s: Seq<M>, m: M) {
                remove sent -= [c => s];
                add    sent += [c => s.push(m)];
            }
        }

        #[invariant]
        pub spec fn wf(&self) -> bool {
            forall|c: ChanId| #[trigger] self.recvd.dom().contains(c) ==>
                self.sent.dom().contains(c)
                && self.recvd[c].len() <= self.sent[c].len()
                && self.recvd[c] =~= self.sent[c].take(self.recvd[c].len() as int)
        }

        #[inductive(do_send)]
        fn do_send_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, m: M) {
            assert forall|k: ChanId| #[trigger] post.recvd.dom().contains(k) implies
                post.sent.dom().contains(k)
                && post.recvd[k].len() <= post.sent[k].len()
                && post.recvd[k] =~= post.sent[k].take(post.recvd[k].len() as int) by {
                if k == c {
                    assert(s.push(m).take(pre.recvd[k].len() as int)
                        =~= s.take(pre.recvd[k].len() as int));
                }
            }
        }

        #[inductive(do_recv)]
        fn do_recv_inductive(pre: Self, post: Self, c: ChanId, s: Seq<M>, r: Seq<M>, m: M) {
            assert(post.recvd[c] =~= s.take(r.len() as int + 1));
        }

        transition!{
            do_recv(c: ChanId, s: Seq<M>, r: Seq<M>, m: M) {
                have   sent >= [c => s];
                remove recvd -= [c => r];
                require(r.len() < s.len() && s[r.len() as int] == m);
                add    recvd += [c => r.push(m)];
            }
        }
    }
}

fn main(){}
