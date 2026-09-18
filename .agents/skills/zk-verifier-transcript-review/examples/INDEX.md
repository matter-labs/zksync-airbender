# Historical transcript and proof-input examples

These examples are transcript-state or proof-input defects recovered from this
repository's Git history. The main table contains only verifier-side failures;
the latent table preserves exact verifier defects not connected to an acceptance
path. `producer-parity/` retains useful prover/GPU/serialization history without
making it part of verifier vulnerability recall. Each case separates invariant,
behavior, reachability, impact, fix, and regression. They are intentionally not
loaded by `SKILL.md`: use them as a regression corpus, not as hints during a
blind review.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Unified prover and verifier disagreed on the family separator](01-unified-family-domain-separator.md) | `7bfd63b` | same-instance transcript parity and universal-mode framing |
| 10 | [Cache-dependency evaluations followed the batching challenge](10-extra-evals-after-batching-challenge.md) | `2df0dea` | wrong Fiat–Shamir order |

## Producer-parity history

These are valuable producer/GPU/serializer bugs for implementation parity and
completeness work. The canonical verifier rejected them or no verifier existed,
so verifier-centric blind evaluation intentionally excludes them.

| # | Example | Fix | Confirmed producer-side scope |
|---:|---|---|---|
| 3 | [Prover-side WHIR OOD point was the constant 42](producer-parity/03-whir-ood-point-constant.md) | `0f645ed` | active prover protocol implementation; no consuming verifier |
| 4 | [Cached dependency evaluations were hashed repeatedly while being collected](producer-parity/04-cache-evaluations-loop-scope.md) | `c9d8620` | active prover transcript construction only |
| 5 | [Recursive WHIR cap was not absorbed](producer-parity/05-recursive-whir-cap-omitted.md) | `66ccc73` | GPU transcript omitted a cap that the verifier bound |
| 6 | [Recursive WHIR OOD value was not absorbed](producer-parity/06-recursive-whir-ood-omitted.md) | `1b2f74f` | GPU transcript omitted a claim that the verifier bound |
| 7 | [Final WHIR monomials were neither serialized nor absorbed](producer-parity/07-final-whir-monomials-omitted.md) | `cb3787d` | GPU emitted an incomplete proof rejected by the verifier |
| 8 | [GPU query drawing advanced the seed by one digest block too many](producer-parity/08-query-word-count-seed-drift.md) | `c1e0576` | GPU/verifier seed mismatch |
| 9 | [Zero-width base cap changed the GPU transcript](producer-parity/09-zero-width-cap-absorption.md) | `6bd4fdf` | GPU/verifier empty-message mismatch |
| 11 | [Attempted cache-ordering repair scoped the batching challenge inside an optional branch](producer-parity/11-batching-challenge-optional-scope.md) | `2df0dea` | noncompiling intermediate prover repair |

## Latent findings

| # | Example | Fix | Activation condition |
|---:|---|---|---|
| 2 | [Unrolled transcript omitted machine-family and inits/teardowns owner tags](latent/02-memory-transcript-family-framing.md) | `386ab26` | connect the private unrolled full-statement verifier and matching prover transform |

Every entry has one primary transcript failure even when the downstream symptom appeared in GKR, WHIR, GPU parity, or L1 generation.
