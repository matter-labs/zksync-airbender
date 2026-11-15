# Historical AIR/STARK, quotient, DEEP-ALI, and FRI examples

This repository's retained legacy history contains fewer confirmed FRI-specific fixes than GKR/WHIR fixes. The main corpus contains two source- and reachability-supported verifier failures. Neither is a standalone FRI-folding bug; they exercise AIR quotient evaluation and generated-verifier layout at the STARK/FRI boundary.

The cards reconstruct the relevant quotient/AIR or generated-verifier boundary, state the intended expression/layout, and separate malformed honest-proof production from acceptance of a false claim. Exact but historically un-emitted or configuration-dependent defects live under `latent/` with activation conditions.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Boundary check read the wrong grand-product column](01-grand-product-boundary-column.md) | `16b5aef` | quotient boundary index |
| 3 | [Empty ABI high limbs were read as real columns](03-empty-abi-offset-column.md) | `613c8de` | optional-column verifier bug |

## Implementation-only history

These generator defects never produced a verifier artifact, so they are useful
generator-review references but not verifier vulnerability examples.

| # | Example | Fix | Why excluded |
|---:|---|---|---|
| 2 | [Sparse delegation quotient scaled the address itself](implementation/02-sparse-delegation-offset.md) | `9b955b6` | affected branch was never emitted into a verifier |
| 4 | [Sparse delegation layout emitted a tuple where an Option was required](implementation/04-sparse-delegation-option-serialization.md) | `9b955b6` | generation failed before a verifier artifact existed |

## Producer-parity history

These cards concern witness construction or setup indexing. A correct verifier
does not accept their malformed output, so they remain references rather than
verifier-centric blind-evaluation targets.

| # | Example | Fix | Producer-side failure |
|---:|---|---|---|
| 5 | [Decoder multiplicities used unrelated fixed domains](producer-parity/05-decoder-multiplicity-domain.md) | `6869368` | latent multiplicity-domain mismatch |
| 6 | [Cached lookup tables used the wrong row order](producer-parity/06-cached-table-row-order.md) | `b6142cd` | lookup witness/setup mismatch |
| 7 | [Circuit-sequence timestamp bound was hardcoded to u16](producer-parity/07-circuit-sequence-timestamp-bound.md) | `3f67e32`, PR #178 | proof-generation completeness failure |

Related circuit-owned cases, such as local AIR constraint omissions, remain in `zk-circuit-review/examples` to keep this corpus focused on the legacy argument and generated verifier. Use the regression sections as cross-implementation oracles: direct AIR evaluation, quotient identities, serialized layout, and verifier evaluation should agree without sharing generated code.
