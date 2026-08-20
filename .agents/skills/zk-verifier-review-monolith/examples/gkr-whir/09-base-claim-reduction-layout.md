# GPU base claims used an incompatible batched reduction

## Classification

- Confirmed historical GKR base-opening implementation bug
- Component: GPU base-layer claim evaluation
- Claim-chain location: final GKR point/eq polynomial → per-column openings → WHIR batch
- Security character: GPU/canonical-verifier incompleteness from a storage-layout/reduction-contract mismatch
- Fixed by: [`6beb5fc`](https://github.com/matter-labs/zksync-airbender/commit/6beb5fccc168f539f073426f3b4f2199b4b18e3b)
- Vulnerable revision: `41464ee88a9bbe40c11a5e296e505e9f09fb90b3`

## Protocol context

At the GKR-to-WHIR boundary, every base column must be evaluated at the final multilinear point. The implementation materializes `eq(row, z)`, multiplies it into each column row, and reduces each weighted column to one extension-field claim:

```text
claim_j = Σ_row column_j[row] * eq(row, z)
```

GPU buffers stored the weighted rows as separate contiguous column vectors. A batched reduction primitive is correct only if its matrix stride/orientation contract matches that physical layout.

## Intended handoff relation

For every memory, witness, or setup column `j`:

```text
weighted_j[row] = value_j[row] * eq[row]
partial_j       = reduce_sum(weighted_j contiguous slice)
claim_j         = Σ row-chunk partial_j
WHIR batch uses exactly claim_j beside commitment to value_j
```

Column count, row-chunk size, and final partial chunk must not change the mapping.

## Failure

The GPU created a matrix view over a buffer whose weighted columns were laid out as independent contiguous vectors, then passed it to `batch_reduce`. The primitive's row/batch interpretation did not match that layout. Its outputs therefore were not guaranteed to equal one dot product per column.

This is a common accelerator bug: elementwise multiplication can be correct, buffer sizes can match, and the reduction can finish without error while summing the wrong strided groups.

## Failure flow

1. Materialize correct equality weights for final GKR point `z`.
2. Write `batch_cols * row_chunk_size` weighted values in column-major contiguous blocks.
3. Reinterpret the buffer as a matrix under `batch_reduce`'s incompatible orientation.
4. Produce partial sums containing values from the wrong rows/columns.
5. Export incorrect base opening claims to WHIR.
6. Canonical verification rejects when committed columns are opened at `z`.

The historical defect is producer incompleteness. If a verifier-side GPU implementation used the same reduction to recompute a public/base claim, an independent scalar oracle would still be required to establish false acceptance.

## Impact and fix

GKR's final claims could be wrong before PCS batching, obscuring the error as a later WHIR opening failure. The fix removes `batch_reduce` and invokes the ordinary one-vector reduction separately on each contiguous weighted column slice.

Every GPU primitive call should carry a storage-shape contract: logical axes, physical strides, batch dimension, reduction axis, and output order. Type-compatible matrix views are not proof of semantic compatibility.

## Regression

- Compare every GPU claim against a CPU scalar dot product.
- Use nonuniform column values and equality weights so row/column transposition is visible.
- Cover one/many columns, uneven batch widths, several row chunks, and final partial batches.
- Assert the WHIR inventory pairs each claim with the commitment to the same column.
- Add a primitive-level layout test independent of the full proof pipeline.

## Reproduction evidence

```sh
git diff 41464ee88a9bbe40c11a5e296e505e9f09fb90b3 6beb5fccc168f539f073426f3b4f2199b4b18e3b -- gpu_prover/src/prover/gkr/base_layer_claims.rs
```
