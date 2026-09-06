# GKR

| Module | Scope |
|---|---|
| [protocol.md](protocol.md) | layer classes, output channels, per-layer messages, and the flattened proof order |
| [verifier.md](verifier.md) | acceptance obligations for the schedule, the channel checks, and the WHIR handoff |
| [soundness.md](soundness.md) | baselines, production deviations, the error terms they require, and the open obligations |

## Reading order

1. [protocol.md](protocol.md) — what the layered object is, what the prover sends per
   layer class, and what the verifier draws.
2. [verifier.md](verifier.md) — the thirteen obligations of the layer verifier and the
   two guarantees it exports.
3. [soundness.md](soundness.md) — which deviations move the construction away from the
   baselines, and what remains unproved.

GKR imports [Sumcheck](../sumcheck/INDEX.md) and draws its challenges from
[transcript/](../transcript/INDEX.md). It consumes the lookup and global-product
relations of [arguments/](../../arguments/INDEX.md) and completes them per proof. Its
base-layer claims are discharged by [WHIR](../whir/INDEX.md).
