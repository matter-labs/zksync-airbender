# Monolithic verifier-review historical corpus

The monolith keeps one self-contained corpus grouped by the same primary failure
domains used by the specialist suite. These are hidden-answer and regression
fixtures, not reference material for an ordinary or blind audit.

| Domain | Cases | Index |
|---|---:|---|
| Transcript and proof inputs | 11 | [transcript](transcript/INDEX.md) |
| Cross-circuit and global composition | 15 | [composition](composition/INDEX.md) |
| Sumcheck, GKR, MLE, and WHIR | 12 | [gkr-whir](gkr-whir/INDEX.md) |
| Legacy AIR, STARK, DEEP-ALI, and FRI | 7 | [stark-fri](stark-fri/INDEX.md) |
| Concrete soundness and grinding | 4 | [soundness](soundness/INDEX.md) |
| Recursion, verifier binaries, and L1 | 16 | [recursion-l1](recursion-l1/INDEX.md) |

Each case is copied from the canonical specialist corpus so the historical
all-in-one skill remains independently benchmarkable. Assign one primary domain
per failure, while allowing the monolithic review itself to follow every seam.
