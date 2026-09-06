# Transcript

| Module | Scope |
|---|---|
| [protocol.md](protocol.md) | initial seed derivation, transcript state transitions, absorbed value encodings, and absorbed order |
| [verifier.md](verifier.md) | statement binding, reduction on read, causality, grinding placement, and source-specific stream termination |
| [soundness.md](soundness.md) | the Fiat-Shamir baseline, production deviations from it, hash assumptions, and open obligations |

## Reading order

1. [protocol.md](protocol.md) — what is absorbed, in what encoding, in what order.
2. [verifier.md](verifier.md) — what a conforming verifier must enforce over that order.
3. [soundness.md](soundness.md) — where the construction departs from the cited
   transformation and what remains unproved.

Every other module in [protocols/](../INDEX.md) draws its challenges from this state
machine.
