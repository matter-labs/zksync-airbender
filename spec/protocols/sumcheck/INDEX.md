# Sumcheck

| Module | Scope |
|---|---|
| [protocol.md](protocol.md) | round structure, message shapes, and data flow |
| [verifier.md](verifier.md) | canonical round and final-relation obligations |
| [soundness.md](soundness.md) | baselines, production deviations, error term, open bound |

## Reading order

1. [protocol.md](protocol.md) — the reduction and its two message shapes.
2. [verifier.md](verifier.md) — the five obligations that [GKR](../gkr/INDEX.md) and
   [WHIR](../whir/INDEX.md) both import, plus the two assumptions they discharge.
3. [soundness.md](soundness.md) — the baselines, what the production form changes, and
   what an instantiation still needs.

Sumcheck draws its coordinates from [transcript/](../transcript/INDEX.md). It defines no
initial or final relation of its own: GKR supplies both in
[gkr/verifier.md](../gkr/verifier.md) and WHIR in
[whir/verifier.md](../whir/verifier.md).
