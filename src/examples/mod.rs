// Example protocols.
//
// Nothing here is part of the library. Each module is a protocol written
// against `crate::tok` and `crate::layer`, kept in the tree because it is
// evidence that the library is usable and because the counterexample suite
// builds on two of them.
//
// Roughly in order of difficulty:
//
//   pingpong         the smallest protocol, written out without the macro
//   lossy            an unreliable link; the smallest complete protocol
//   heartbeat        sole-sender ownership across an interference point
//   collector        many producers, one consumer, unordered delivery
//   twophase_fanout  two-phase commit by broadcast and gather
//   twophase         two-phase commit by remote call, with minted channels
//   chang_roberts    ring leader election
//
// and three that exercise the library rather than a protocol:
//
//   compose          two protocols on one thread
//   multithread      one process, several threads
//   layers_demo      refinement up to an abstract model

pub mod pingpong;
pub mod lossy;
pub mod heartbeat;
pub mod collector;
pub mod twophase_fanout;
pub mod twophase;
pub mod chang_roberts;
pub mod leaselock;
pub mod compose;
pub mod multithread;
pub mod layers_demo;
pub mod system;
pub mod lease_system;
pub mod paxos;
pub mod paxos_system;
pub mod rbc;
pub mod abd;
pub mod abd_hb;
