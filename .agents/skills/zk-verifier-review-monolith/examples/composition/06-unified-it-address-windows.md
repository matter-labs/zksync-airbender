# Unified inits/teardowns used placeholder address windows

## Classification

- Confirmed historical unified-memory composition bug
- Fixed by: [`1581753`](https://github.com/matter-labs/zksync-airbender/commit/158175327734b2b865deb24dd7ea5a1b063abd65), PR [#389](https://github.com/matter-labs/zksync-airbender/pull/389)
- Vulnerable revision: `ae3c9adba438afbce0a2d94d91931dfd8082c2bd`

## Failure

Unified GPU proving supplied canonical `0..num_sets` placeholders for inits/teardowns `top_bits`. Those values describe a dedicated 16-set circuit, not the unified circuit's two-set instances spread across 32 RAM windows; page indices also used the wrong geometry.

## Impact and fix

The committed address partitions did not cover the same RAM relation as execution chunks, so the global permutation could not close. The fix binds real per-instance windows and local page indices.

## Regression

Check complete, disjoint coverage of all unified RAM windows and close the global product with nontrivial touched pages in each window.

```sh
git diff ae3c9adba438afbce0a2d94d91931dfd8082c2bd 158175327734b2b865deb24dd7ea5a1b063abd65 -- gpu/circuit_prover/src/proof/inputs.rs gpu/execution_prover/src/prover/pipeline.rs
```
