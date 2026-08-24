# spike

Standalone experiments, each verified on its own (`verus spike/<f>.rs
--crate-type=bin`). Not part of `src/main.rs`. Kept because `docs/plan.md`
cites them as the evidence for design decisions.

| file | question it answered |
|---|---|
| `s1.rs` | generic `M`, map-sharded `Map<ChanId, Seq<M>>`, `#[invariant]` + `#[inductive]` |
| `s2.rs` | `persistent_set` for monotone "was sent", duplicable via `.clone()` |
| `s3.rs` | `split_token` / `merge_token` as *proved* operations (`SetToken::remove`/`insert`) |
| `s4.rs` | the `Spec` / `Protocol` trait split, stuttering, a Leslie-shaped abstract state |
| `example_vote.rs` | the whole design end to end on a two-node protocol |
| `example_rpc.rs` | the RPC trick in the token setting; `absorb_handler` as a proof fn |
| `counter.rs` | the small tokenized state machine printed in the appendix of `docs/movers.pdf`, kept here so the document's example stays checked |

Removed once their content landed in `src/`: the `ChanTokens` feasibility spike
(now `src/tok.rs`), the layering-over-a-machine-state spike (now
`src/layers_demo.rs`), and a scratch state machine used while porting
`twophase`.
