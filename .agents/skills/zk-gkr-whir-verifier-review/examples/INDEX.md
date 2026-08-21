# Historical GKR, Sumcheck, MLE, and WHIR examples

These examples concern protocol algebra, fold conventions, query geometry, or the immediate GKR-to-WHIR handoff. Transcript-only omissions and global-composition failures are indexed by their own specialists.

The main corpus contains only defects with a completed proof-producing path or
an established honest-proof/component acceptance failure. Cards distinguish
historical producer completeness from verifier false acceptance; a hypothetical
verifier sharing a prover bug is not classified as historical soundness impact.

Exact defects from unfinished proof paths live under `latent/`, with their
activation conditions. Semantically unproven rewrites live under
`implementation/` and are excluded from blind vulnerability evaluation.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [MaxQuadratic reused terms and polluted the quadratic coefficient](01-maxquadratic-coefficients.md) | `a514b2d` | wrong sumcheck polynomial |
| 2 | [Batched sumcheck used the wrong last-round convention](02-last-round-quadratic-convention.md) | `42e910a` | final round interpolation mismatch |
| 3 | [WHIR batching zeroed every power but the first](03-whir-batching-powers-zeroed.md) | `c9d8620` | unbound batched oracles |
| 4 | [WHIR delinearization reused one power](04-whir-delinearization-powers.md) | `e865551` | incorrect random linear combination |
| 5 | [Base-field WHIR path used the wrong coset layout](05-base-whir-merkle-path-layout.md) | `f2ce204` | leaf/path position mismatch |
| 6 | [Extension WHIR path used the raw folded index](06-extension-whir-merkle-path-index.md) | `a07715f` | path index mismatch |
| 7 | [WHIR proof recorded raw rather than tree-space query indices](07-whir-recorded-query-index.md) | `2961e73` | proof/index semantics mismatch |
| 10 | [Proof-slab parsing dropped final WHIR fields](10-whir-slab-field-loss.md) | `7fe3e70` | GKR-to-PCS serialization loss |

## Latent defects

| # | Example | Fix | Activation condition |
|---:|---|---|---|
| 8 | [Multilinear coefficients were built in the wrong bit order](latent/08-whir-rs-bit-order.md) | `619c6ab` | complete the then-`todo!()` proof assembly |
| 11 | [Unbalanced LogUp corrupted the quadratic coefficient and extension addition](latent/11-logup-quadratic-coefficient-and-add-helper.md) | `a1ae551` | expose the affected pre-assembly relation through a proof-producing entrypoint |
| 12 | [Dimension reduction confused output and input indices](latent/12-dimension-reduction-index-space.md) | `5df7abb` | complete the then-`todo!()` proof assembly |

## Implementation-only history

| # | Example | Change | Why excluded |
|---:|---|---|---|
| 9 | [Base-claim reduction was rewritten without a demonstrated semantic defect](implementation/09-base-claim-reduction-rewrite.md) | `6beb5fc` | the claimed layout mismatch contradicts the source contracts; no distinct runtime failure is established |

The verifier-side audit lesson is the same for prover-parity cases:
independently recompute the claimed polynomial, index, or fold relation; do not
make acceptance track a shared buggy producer. During blind evaluation, the
historical patch is evidence for the bug shape—not permission to report a
producer defect as verifier soundness without tracing the accepting predicate.
