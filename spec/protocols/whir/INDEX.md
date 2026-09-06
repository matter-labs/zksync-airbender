# WHIR

| Module | Scope |
|---|---|
| [protocol.md](protocol.md) | message polynomial, per-round wire order, oracle and leaf geometry |
| [verifier.md](verifier.md) | canonical fold, authentication, composition, and final-check obligations |
| [soundness.md](soundness.md) | baseline, production deviations, per-round error terms, open bounds |

## Reading order

1. [protocol.md](protocol.md) — what one round puts on the wire, and how the production
   round boundary is cut one step earlier than the baseline's.
2. [verifier.md](verifier.md) — the ten obligations, including the accumulated weighted
   sum that distinguishes WHIR acceptance from a FRI-style query loop.
3. [soundness.md](soundness.md) — which error terms the selected schedules budget and
   which they leave to the field size.

WHIR imports [Sumcheck](../sumcheck/INDEX.md) and [transcript/](../transcript/INDEX.md),
and discharges the batched claim produced by [GKR](../gkr/INDEX.md). Its concrete
schedule is selected in [soundness parameters](../../soundness/parameters.md); no value
of that schedule is carried by a proof.
