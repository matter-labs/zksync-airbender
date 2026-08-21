# Historical transcript and proof-input examples

These examples are transcript-state or prover-input defects recovered from this
repository's Git history. The main table contains only reachable historical
soundness or honest-proof/completeness failures. The implementation table keeps
exact active code defects for which neither acceptance nor rejection was
established. The latent table preserves exact defects that were not connected
to an acceptance or proof-production path in the reviewed revision. Each case
separates invariant, behavior, reachability, impact, fix, and regression. They
are intentionally not loaded by `SKILL.md`: use them as a regression corpus,
not as hints during a blind review.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Unified prover and verifier disagreed on the family separator](01-unified-family-domain-separator.md) | `7bfd63b` | same-instance transcript parity and universal-mode framing |
| 5 | [Recursive WHIR cap was not absorbed](05-recursive-whir-cap-omitted.md) | `66ccc73` | missing commitment absorption |
| 6 | [Recursive WHIR OOD value was not absorbed](06-recursive-whir-ood-omitted.md) | `1b2f74f` | missing prover-message absorption |
| 7 | [Final WHIR monomials were neither serialized nor absorbed](07-final-whir-monomials-omitted.md) | `cb3787d` | missing final message and absorption |
| 8 | [GPU query drawing advanced the seed by one digest block too many](08-query-word-count-seed-drift.md) | `c1e0576` | squeeze-length mismatch |
| 9 | [Zero-width base cap changed the GPU transcript](09-zero-width-cap-absorption.md) | `6bd4fdf` | empty/optional-path mismatch |
| 10 | [Cache-dependency evaluations followed the batching challenge](10-extra-evals-after-batching-challenge.md) | `2df0dea` | wrong Fiat-Shamir order |

## Implementation-only defects

These are concrete implementation bugs, but the reviewed revision did not
establish a verifier acceptance path or soundness vulnerability. Do not count
them as primary vulnerability recall.

| # | Example | Fix | Confirmed scope |
|---:|---|---|---|
| 3 | [Prover-side WHIR OOD point was the constant 42](implementation/03-whir-ood-point-constant.md) | `0f645ed` | active prover protocol implementation; no consuming verifier |
| 4 | [Cached dependency evaluations were hashed repeatedly while being collected](implementation/04-cache-evaluations-loop-scope.md) | `c9d8620` | active prover transcript construction only |

## Latent findings

| # | Example | Fix | Activation condition |
|---:|---|---|---|
| 2 | [Unrolled transcript omitted machine-family and inits/teardowns owner tags](latent/02-memory-transcript-family-framing.md) | `386ab26` | connect the private unrolled full-statement verifier and matching prover transform |
| 11 | [Attempted cache-ordering repair scoped the batching challenge inside an optional branch](latent/11-batching-challenge-optional-scope.md) | `2df0dea` | make the intermediate prover revision compile without moving the transition |

Every entry has one primary transcript failure even when the downstream symptom appeared in GKR, WHIR, GPU parity, or L1 generation.
