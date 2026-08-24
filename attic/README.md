# attic

Superseded by the tokenized state-machine model in `src/`. Kept because the
material is still readable evidence of what changed, not because anything
depends on it. Nothing here is built or verified by `src/main.rs`.

| file | why it is here |
|---|---|
| `net.rs` | Network ghost state as a single global `Net<M>`, plus the `ChannelModel` trait and its `Fifo` / `Bag` / `LossyBag` instances. Superseded by per-protocol state machines; the delivery discipline now lives in `ChanTokens::deliverable_at` / `after_recv`, which is one line per model instead of six lemmas. |
| `api.rs` | The `Protocol` trait with footprints and the five mover obligations; `NetToken`; `env_step`; `Handler` / `rpc`; `split_token` / `merge_token`. Framing is now structural (you can only touch channels whose tokens you hold), so `env_step` and the pool obligations have no counterpart. `rpc` survives, generically, in `src/tok.rs`. |
| `twophase_legacy.rs` | Two-phase commit against the old `Protocol` API, including the `TpcAbs` layer. Superseded by `src/twophase.rs`; the layering it demonstrated is now in `src/layers_demo.rs`. |
| `nonlocal_gate.rs` | A counterexample: an action gated on a channel outside its footprint. **No longer expressible.** A gate is handed only the channel it is about, so it cannot read another channel's state. The API prevents by construction what this file used to catch. |
| `understated_footprint.rs` | A counterexample: an action writing outside its declared footprint. **No longer expressible.** There are no footprints; a thread can only write a channel whose token it holds. |

The two counterexamples are the clearest measure of the change: both tested
obligations that the token model does not have, because it makes the underlying
mistakes unrepresentable rather than checkable. What is still worth catching is
the gate, and `counterexamples/dishonest_participant.rs` does that.
