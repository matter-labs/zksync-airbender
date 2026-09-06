# Protocols

> Proof-system protocols shared by every proving mode: the Fiat-Shamir transcript, the
> Sumcheck reduction, the GKR layer reduction, and the WHIR polynomial-commitment
> opening. Machine and argument relations are not specified here.

## Modules

| Module | Scope |
|---|---|
| [transcript/](transcript/INDEX.md) | message order, challenge derivation, and proof-of-work placement |
| [sumcheck/](sumcheck/INDEX.md) | one-variable-per-round polynomial-sum reduction and its verifier |
| [gkr/](gkr/INDEX.md) | layered-circuit reduction, layer batching, and the WHIR handoff |
| [whir/](whir/INDEX.md) | committed-polynomial opening proof, folding schedule, and query authentication |

Each module carries `protocol.md` (construction and data flow), `verifier.md`
(canonical acceptance obligations), and `soundness.md` (baseline references,
assumptions, and open obligations).

## Reading order

1. [transcript/](transcript/INDEX.md) — every later challenge and nonce is defined
   relative to this state machine.
2. [sumcheck/](sumcheck/INDEX.md) — the round relation reused by both GKR and WHIR.
3. [gkr/](gkr/INDEX.md) — consumes the transcript and Sumcheck obligations and produces
   the batched base-layer opening claim.
4. [whir/](whir/INDEX.md) — discharges that opening claim.

## Consumers

The [full-statement verifier](../recursion/full-statement-verifier/INDEX.md) invokes
these protocols once per participating proof: it supplies the public statement and
external challenges to the transcript, runs the GKR verifier over the selected compiled
circuit, and accepts only after the WHIR opening for that circuit's base oracles has
been verified. Concrete fold, query, and proof-of-work values are not fixed here; they
are selected per target in [soundness parameters](../soundness/parameters.md).
