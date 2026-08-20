# Historical AIR/STARK, quotient, DEEP-ALI, and FRI examples

This repository's retained legacy history contains fewer confirmed FRI-specific fixes than GKR/WHIR fixes. These seven cases are the high-confidence legacy argument/verifier failures; no speculative WIP commits were added merely to reach a quota.

The cards reconstruct the relevant quotient/AIR or generated-verifier boundary, state the intended expression/layout, and separate malformed honest-proof production from acceptance of a false claim. This is especially important for generator fixes: a bad quotient term usually causes a correct verifier to reject, while soundness impact requires the verifier or generated artifact to enforce the same wrong relation.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Boundary check read the wrong grand-product column](01-grand-product-boundary-column.md) | `16b5aef` | quotient boundary index |
| 2 | [Sparse delegation quotient scaled the address itself](02-sparse-delegation-offset.md) | `9b955b6` | wrong quotient expression |
| 3 | [Empty ABI high limbs were read as real columns](03-empty-abi-offset-column.md) | `613c8de` | optional-column verifier bug |
| 4 | [Sparse delegation layout emitted a tuple where an Option was required](04-sparse-delegation-option-serialization.md) | `9b955b6` | malformed verifier artifact |
| 5 | [Decoder multiplicities used timestamp-domain size](05-decoder-multiplicity-domain.md) | `6869368` | lookup table/domain mismatch |
| 6 | [Cached lookup tables used the wrong row order](06-cached-table-row-order.md) | `b6142cd` | multiplicity/index mismatch |
| 7 | [Circuit-sequence timestamp bound was hardcoded to u16](07-circuit-sequence-timestamp-bound.md) | `3f67e32`, PR #178 | large-trace completeness bug |

Related circuit-owned cases, such as local AIR constraint omissions, remain in `zk-circuit-review/examples` to keep this corpus focused on the legacy argument and generated verifier. Use the regression sections as cross-implementation oracles: direct AIR evaluation, quotient identities, serialized layout, and verifier evaluation should agree without sharing generated code.
