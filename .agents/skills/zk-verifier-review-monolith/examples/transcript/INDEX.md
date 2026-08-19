# Historical transcript and proof-input examples

These examples are confirmed transcript-state or prover-input bugs recovered from this repository's Git history. They are intentionally not loaded by `SKILL.md`: use them as a regression corpus, not as hints during a blind review.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Unified circuit family was not transcript-bound](01-unified-family-domain-separator.md) | `7bfd63b` | missing statement/domain binding |
| 2 | [Memory transcript omitted family/type framing](02-memory-transcript-family-framing.md) | `386ab26` | ambiguous/incomplete absorption |
| 3 | [WHIR OOD point was the constant 42](03-whir-ood-point-constant.md) | `0f645ed` | challenge not sampled |
| 4 | [Cached evaluations were absorbed in the wrong scope](04-cache-evaluations-loop-scope.md) | `c9d8620` | branch/loop transcript drift |
| 5 | [Recursive WHIR cap was not absorbed](05-recursive-whir-cap-omitted.md) | `66ccc73` | missing commitment absorption |
| 6 | [Recursive WHIR OOD value was not absorbed](06-recursive-whir-ood-omitted.md) | `1b2f74f` | missing prover-message absorption |
| 7 | [Final WHIR monomials were not absorbed](07-final-whir-monomials-omitted.md) | `cb3787d` | challenge drawn before final message |
| 8 | [GPU query draw advanced one digest too far](08-query-word-count-seed-drift.md) | `c1e0576` | squeeze-length mismatch |
| 9 | [Zero-width base cap changed the GPU transcript](09-zero-width-cap-absorption.md) | `6bd4fdf` | empty/optional-path mismatch |
| 10 | [Cache-dependency evaluations followed the batching challenge](10-extra-evals-after-batching-challenge.md) | `4e3142e` | wrong Fiat-Shamir order |
| 11 | [Batching challenge lived inside an optional cache branch](11-batching-challenge-optional-scope.md) | `2df0dea` | optional-path challenge bug |

Every entry has one primary transcript failure even when the downstream symptom appeared in GKR, WHIR, GPU parity, or L1 generation.
