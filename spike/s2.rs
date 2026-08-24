#![allow(unused_imports)]
use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

verus!{ pub type ChanId = nat; }

tokenized_state_machine!{
    BagSM<M> {
        fields {
            /// Monotone knowledge: (channel, message) was sent. Duplicable,
            /// never removed. No exclusive send-side token: bag channels have
            /// many senders and nobody needs to know the exact history.
            #[sharding(persistent_set)]
            pub was_sent: Set<(ChanId, M)>,

            /// Exclusive: the unique consumer's record.
            #[sharding(map)]
            pub recvd: Map<ChanId, Seq<M>>,

            /// Endpoint ownership, split across sibling threads.
            #[sharding(set)]
            pub recv_owned: Set<ChanId>,
        }

        transition!{
            do_send(c: ChanId, m: M) {
                add was_sent (union)= set { (c, m) };
            }
        }

        transition!{
            do_recv(c: ChanId, r: Seq<M>, m: M) {
                have   was_sent >= set { (c, m) };
                have   recv_owned >= set { c };
                remove recvd -= [c => r];
                add    recvd += [c => r.push(m)];
            }
        }
    }
}

verus!{
/// Can a receiver recover "what I got was sent" from a persistent fact alone?
proof fn use_persistent<M>(
    tracked inst: BagSM::Instance<M>,
    tracked f: BagSM::was_sent<M>,
)
    requires f.instance_id() == inst.id(),
{
    // persistent tokens are duplicable
    let tracked g = f.clone();
    assert(g.element() == f.element());
}
}
fn main(){}
