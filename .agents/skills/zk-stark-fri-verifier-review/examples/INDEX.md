# Historical AIR/STARK, quotient, DEEP-ALI, and FRI examples

This repository's retained legacy history contains fewer confirmed FRI-specific fixes than GKR/WHIR fixes. The main corpus contains five source- and reachability-supported legacy argument, verifier, or generator failures. None is a standalone FRI-folding bug; they exercise AIR quotient generation, lookup construction, generated-verifier layout, and proving bounds at the STARK/FRI boundary.

The cards reconstruct the relevant quotient/AIR or generated-verifier boundary, state the intended expression/layout, and separate malformed honest-proof production from acceptance of a false claim. Exact but historically un-emitted or configuration-dependent defects live under `latent/` with activation conditions.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Boundary check read the wrong grand-product column](01-grand-product-boundary-column.md) | `16b5aef` | quotient boundary index |
| 3 | [Empty ABI high limbs were read as real columns](03-empty-abi-offset-column.md) | `613c8de` | optional-column verifier bug |
| 4 | [Sparse delegation layout emitted a tuple where an Option was required](04-sparse-delegation-option-serialization.md) | `9b955b6` | malformed verifier artifact |
| 6 | [Cached lookup tables used the wrong row order](06-cached-table-row-order.md) | `b6142cd` | multiplicity/index mismatch |
| 7 | [Circuit-sequence timestamp bound was hardcoded to u16](07-circuit-sequence-timestamp-bound.md) | `3f67e32`, PR #178 | large-trace completeness bug |

## Latent defects

| # | Example | Fix | Activation condition |
|---:|---|---|---|
| 2 | [Sparse delegation quotient scaled the address itself](latent/02-sparse-delegation-offset.md) | `9b955b6` | emit and compile a variable-dependent sparse verifier after clearing the separate serializer blocker |
| 5 | [Decoder multiplicities used unrelated fixed domains](latent/05-decoder-multiplicity-domain.md) | `6869368` | use a supported decoder table with nonzero rows outside the old fixed allocation/write range |

Related circuit-owned cases, such as local AIR constraint omissions, remain in `zk-circuit-review/examples` to keep this corpus focused on the legacy argument and generated verifier. Use the regression sections as cross-implementation oracles: direct AIR evaluation, quotient identities, serialized layout, and verifier evaluation should agree without sharing generated code.
