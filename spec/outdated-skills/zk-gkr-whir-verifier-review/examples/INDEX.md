# Historical GKR, Sumcheck, MLE, and WHIR examples

These examples concern protocol algebra, fold conventions, query geometry, or the immediate GKR-to-WHIR handoff. Transcript-only omissions and global-composition failures are indexed by their own specialists.

## Verifier vulnerabilities

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 13 | [Generated GKR verifier did not pin virtual setup polynomial evaluations](13-virtual-setup-evaluations-unpinned.md) | `287ba6d`, PR #282 | uncommitted layer-0 claims were not verifier-computed or PCS-authenticated |

Other verifier bugs occurred inside GKR/WHIR code but are owned by their primary
specialists to avoid duplicate examples: transcript example 10 covers late GKR
cache evaluations, soundness example 3 covers GKR/WHIR grinding, and
recursion/L1 examples 1, 2, and 6 cover generated EVM GKR acceptance.

## Producer-parity history

The remaining retained cards concern proof construction, GPU layout,
serialization, or unfinished prover paths. A canonical verifier rejects the bad
output. They are useful protocol seam references but are excluded from
verifier-centric blind evaluation.

| # | Example | Fix | Producer-side failure |
|---:|---|---|---|
| 1 | [MaxQuadratic reused terms and polluted the quadratic coefficient](producer-parity/01-maxquadratic-coefficients.md) | `a514b2d` | wrong round polynomial |
| 2 | [Batched sumcheck used the wrong last-round convention](producer-parity/02-last-round-quadratic-convention.md) | `42e910a` | incompatible terminal encoding |
| 3 | [WHIR batching zeroed every power but the first](producer-parity/03-whir-batching-powers-zeroed.md) | `c9d8620` | malformed opening reduction |
| 4 | [WHIR delinearization reused one power](producer-parity/04-whir-delinearization-powers.md) | `e865551` | malformed linear combination |
| 5 | [Base-field WHIR path used the wrong coset layout](producer-parity/05-base-whir-merkle-path-layout.md) | `f2ce204` | wrong leaf/path construction |
| 6 | [Extension WHIR path used the raw folded index](producer-parity/06-extension-whir-merkle-path-index.md) | `a07715f` | wrong path construction |
| 7 | [WHIR proof recorded raw rather than tree-space query indices](producer-parity/07-whir-recorded-query-index.md) | `2961e73` | proof/index mismatch |
| 8 | [Multilinear coefficients were built in the wrong bit order](producer-parity/08-whir-rs-bit-order.md) | `619c6ab` | latent encoding defect |
| 9 | [Base-claim reduction was rewritten without a demonstrated semantic defect](producer-parity/09-base-claim-reduction-rewrite.md) | `6beb5fc` | unproven implementation change |
| 10 | [Proof-slab parsing dropped final WHIR fields](producer-parity/10-whir-slab-field-loss.md) | `7fe3e70` | serialized proof corruption |
| 11 | [Unbalanced LogUp corrupted the quadratic coefficient and extension addition](producer-parity/11-logup-quadratic-coefficient-and-add-helper.md) | `a1ae551` | latent round-polynomial defect |
| 12 | [Dimension reduction confused output and input indices](producer-parity/12-dimension-reduction-index-space.md) | `5df7abb` | latent layer-mapping defect |

The verifier-side audit lesson is the same for prover-parity cases:
independently recompute the claimed polynomial, index, or fold relation; do not
make acceptance track a shared buggy producer. During blind evaluation, the
historical patch is evidence for the bug shape—not permission to report a
producer defect as verifier soundness without tracing the accepting predicate.
