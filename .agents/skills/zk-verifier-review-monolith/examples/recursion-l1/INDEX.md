# Historical recursion, verifier-binary, and L1/EVM examples

These examples focus on acceptance boundaries: recursive public outputs, generated verifier identity, calldata consumption, Solidity/Yul checks, and proof-chain state. Generic transcript cases are not duplicated unless the failure is specific to the L1 handoff.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [EVM verifier omitted all LogUp identity checks](01-evm-logup-identities.md) | `bf9bd04` | missing acceptance gate |
| 2 | [EVM batching challenge preceded cache-dependency evaluations](02-evm-cache-evals-order.md) | `4b0d431` | L1 transcript mismatch |
| 3 | [WHIR contract accepted trailing proof calldata](03-evm-trailing-calldata.md) | `4b0d431` | incomplete proof consumption |
| 4 | [EVM layer-0 opening list stopped at 72 instead of 113](04-evm-layer0-opening-count.md) | `16a5ceb` | partial claim binding |
| 5 | [Yul sumcheck failures were stored but never rejected](05-yul-nonfailing-checks.md) | `4f8d993` | fail-open verification |
| 6 | [Generated EVM verifier hardcoded layer count and output order](06-evm-generated-layer-order.md) | `5459c07` | artifact/generator drift |
| 7 | [EVM WHIR calldata ignored the configured round schedule](07-evm-whir-schedule-hardcoded.md) | `1f8cb3c` | proof/config mismatch |
| 8 | [L1 transcript omitted final registers, PC, and timestamp](08-l1-final-state-transcript.md) | `f15c643` | public-state binding gap |
| 9 | [L1 inits/teardowns product ratio was reversed](09-l1-it-product-orientation.md) | `f15c643` | recursive accumulator orientation |
| 10 | [Recursive Blake leaf verifier mishandled one full block](10-recursive-blake-full-block.md) | `0e81150` | binary hash mismatch |
| 11 | [Keccak recursion boundary timestamp was one cycle late](11-keccak-recursion-timestamp.md) | `93e124e` | recursive public-state mismatch |
| 12 | [Yul cached gate values were not reduced modulo the field](12-yul-cache-canonicalization.md) | `fe19aa2` | noncanonical field cache |
| 13 | [Recursive proof output was not bound to the supplied program](13-recursion-program-binding.md) | `a2d7ad1`, PR #321 | cross-program replay |
| 14 | [Verification policy came from prover-controlled metadata](14-artifact-policy-downgrade.md) | `3e53f3f`, PR #329 | policy downgrade |
| 15 | [Unrolled recursion was not bound to the wrapped stage](15-unrolled-stage-binding.md) | `3e53f3f`, PR #329 | recursion-depth confusion |
| 16 | [Unified recursion did not enforce terminal convergence](16-unified-convergence.md) | `3e53f3f`, PR #329 | intermediate-as-final acceptance |

Early EVM work was prototype code, but each entry records a concrete pre-fix semantic failure rather than a generic unfinished feature.
