# GPU base claims used an incompatible batched reduction

## Classification

- Confirmed historical GKR base-opening implementation bug
- Fixed by: [`6beb5fc`](https://github.com/matter-labs/zksync-airbender/commit/6beb5fccc168f539f073426f3b4f2199b4b18e3b)
- Vulnerable revision: `41464ee88a9bbe40c11a5e296e505e9f09fb90b3`

## Failure

GPU base-layer claim evaluation fed a matrix view to `batch_reduce` even though the weighted columns were laid out as separate contiguous vectors under a different reduction contract. Column sums therefore did not reliably equal the MLE dot products.

## Impact and fix

The GKR-to-WHIR opening claims could be wrong before PCS batching. The fix reduces each contiguous weighted column explicitly with the ordinary reduction primitive.

## Regression

Compare every column claim to a CPU dot product for uneven batch widths, multiple row chunks, and nonuniform eq weights.

```sh
git diff 41464ee88a9bbe40c11a5e296e505e9f09fb90b3 6beb5fccc168f539f073426f3b4f2199b4b18e3b -- gpu_prover/src/prover/gkr/base_layer_claims.rs
```
