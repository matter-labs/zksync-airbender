# Historical GKR, Sumcheck, MLE, and WHIR examples

These examples concern protocol algebra, fold conventions, query geometry, or the immediate GKR-to-WHIR handoff. Transcript-only omissions and global-composition failures are indexed by their own specialists.

Each card now records the bounded claim boundary, intended algebra/index convention, concrete failure flow, verifier-side acceptance consequences, and regression strategy. Several fixes repaired an honest prover or serializer; those cards explicitly distinguish producer parity/completeness from false acceptance and explain what additional shared-verifier defect would turn the mismatch into soundness impact.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [MaxQuadratic reused terms and polluted the quadratic coefficient](01-maxquadratic-coefficients.md) | `a514b2d` | wrong sumcheck polynomial |
| 2 | [Batched sumcheck used the wrong last-round convention](02-last-round-quadratic-convention.md) | `42e910a` | final round interpolation mismatch |
| 3 | [WHIR batching zeroed every power but the first](03-whir-batching-powers-zeroed.md) | `c9d8620` | unbound batched oracles |
| 4 | [WHIR delinearization reused one power](04-whir-delinearization-powers.md) | `e865551` | incorrect random linear combination |
| 5 | [Base-field WHIR path used the wrong coset layout](05-base-whir-merkle-path-layout.md) | `f2ce204` | leaf/path position mismatch |
| 6 | [Extension WHIR path used the raw folded index](06-extension-whir-merkle-path-index.md) | `a07715f` | path index mismatch |
| 7 | [WHIR proof recorded raw rather than tree-space query indices](07-whir-recorded-query-index.md) | `2961e73` | proof/index semantics mismatch |
| 8 | [Multilinear coefficients were built in the wrong bit order](08-whir-rs-bit-order.md) | `619c6ab` | MLE/RS ordering mismatch |
| 9 | [GPU base claims used an incompatible batched reduction](09-base-claim-reduction-layout.md) | `6beb5fc` | wrong MLE opening claim |
| 10 | [Proof-slab parsing dropped final WHIR fields](10-whir-slab-field-loss.md) | `7fe3e70` | GKR-to-PCS serialization loss |
| 11 | [Unbalanced LogUp kernel added gamma twice](11-logup-additive-challenge-double-count.md) | `a1ae551` | wrong sumcheck gate polynomial |
| 12 | [Dimension reduction confused output and input indices](12-dimension-reduction-index-space.md) | `5df7abb` | GKR layer index mismatch |

The verifier-side audit lesson is the same for prover-parity cases: independently recompute the claimed polynomial, index, or fold relation; do not make acceptance track a shared buggy producer. During blind evaluation, the historical patch is evidence for the bug shape—not permission to report the producer defect as verifier soundness without tracing the accepting predicate.
