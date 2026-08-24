#![allow(unused_imports)]
use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

tokenized_state_machine!{
    Counter {
        fields {
            #[sharding(variable)] pub total: nat,   // one exclusive token
            #[sharding(count)]    pub units: nat,   // splittable into shares
        }

        #[invariant]
        pub spec fn agree(&self) -> bool { self.total == self.units }

        init!{
            boot() { init total = 0; init units = 0; }
        }

        transition!{
            incr() {
                update total = pre.total + 1;       // change an exclusive field
                add    units += (1);                // mint one share
            }
        }

        #[inductive(boot)]  fn boot_inductive(post: Self) { }
        #[inductive(incr)]  fn incr_inductive(pre: Self, post: Self) { }
    }
}
fn main(){}
