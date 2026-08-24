use vstd::prelude::*;
use crate::tok::*;
use crate::proc::*;
use crate::examples::heartbeat::{Beat, HbTok, link as hb_link};
use crate::examples::lossy::{Pkt, Lossy, ok, link};

verus! {

/// One service running two unrelated protocols.
///
/// There is no composition obligation of any kind. The two instances cannot
/// interfere, so this service's invariant is the conjunction of the two
/// independent invariants and nothing else, and the proof is the two
/// independent proofs side by side.
pub struct BothLinks {
    pub hb: Out<Beat, HbTok>,
    pub lo: Out<Pkt, Lossy>,
    pub seq: u64,
    pub v: u64,
}

impl BothLinks {
    pub open spec fn inv(&self) -> bool {
        // The heartbeat half ...
        &&& self.hb.wf() && self.hb.id() == hb_link()
        &&& forall|x: int| 0 <= x < self.hb.hist().len()
                ==> (#[trigger] self.hb.hist()[x]).seq < self.seq
        // ... and the lossy half. Nothing relates them.
        &&& self.lo.wf() && self.lo.id() == link()
        &&& ok(self.v)
    }

    pub fn send_both(&mut self)
        requires old(self).inv(), old(self).seq < u64::MAX,
        ensures
            final(self).inv(),
            final(self).hb.hist() == old(self).hb.hist().push(Beat { seq: old(self).seq }),
            final(self).lo.hist() == old(self).lo.hist().push(Pkt { v: old(self).v }),
    {
        let s = self.seq;
        let ghost h0 = self.hb.hist();
        self.hb.send(Beat { seq: s });

        interference_point();

        self.lo.send(Pkt { v: self.v });
        self.seq = s + 1;
        assert forall|x: int| 0 <= x < self.hb.hist().len()
            implies (#[trigger] self.hb.hist()[x]).seq < self.seq by {
            if x < h0.len() { assert(self.hb.hist()[x] == h0[x]); }
        }
    }
}

impl Process for BothLinks {
    open spec fn wf(&self) -> bool { self.inv() }
    fn step(&mut self) {
        if self.seq < u64::MAX { self.send_both(); }
    }
}

} // verus!
