# Base-claim reduction was rewritten without a demonstrated semantic defect

## Classification

- Producer-parity history: historical implementation change; excluded from the vulnerability corpus
- Component: GPU base-layer claim reduction
- Claim-chain location: weighted column rows → one claimed MLE evaluation per column
- Security character: unproven; the source-visible before/after implementations have the same reduction contract
- Fixed by: [`6beb5fc`](https://github.com/matter-labs/zksync-airbender/commit/6beb5fccc168f539f073426f3b4f2199b4b18e3b) (historical commit label; vulnerability status unproven)
- Vulnerable revision: `41464ee88a9bbe40c11a5e296e505e9f09fb90b3`
- Fixture caveat: the revision is retained for evaluation reproducibility; vulnerability status is unproven

## What changed

For each contiguous weighted column, the earlier implementation constructed a
`DeviceMatrixMut` with `stride = row_chunk_size` and called segmented
`batch_reduce`. The patch instead constructs one `DeviceVectorChunk` per column
and calls ordinary `reduce` repeatedly.

Both paths are intended to compute:

```text
claim_j = sum_row column_j[row] * eq(row, z)
```

The segmented reducer defines one segment per matrix column, with segment
offsets separated by the matrix stride. Given the constructed matrix's stride,
those segments are precisely the same contiguous column slices used after the
patch. The repository also had direct batch-reduction tests for extension-field
inputs.

## Why the former card was invalid

The former example asserted a row/column orientation mismatch. The actual
`DeviceMatrixMut`, `DeviceMatrixChunkImpl`, and CUDA segmented-reduction
contracts do not support that claim: the matrix is column-major, its stride is
the contiguous column length, and `batch_reduce` reduces each such segment.

The terse commit title says `fix`, but provides no failure mode, failing test,
runtime condition, or explanation of a lower-level segmented-reduction defect.
Replacing a batched operation with semantically equivalent scalar operations is
not by itself evidence of wrong claims, honest-proof rejection, or false
acceptance.

## Failure

No vulnerability mechanism is established by the available history. The only
confirmed fact is a replacement of segmented reductions with per-column
reductions; the former card's claimed layout mismatch is inconsistent with the
source-visible stride and segment semantics.

## Impact and fix

No soundness or completeness impact is currently supported. Treat `6beb5fc` as
an implementation rewrite unless additional runtime evidence identifies a
distinct lower-level failure and connects it to incorrect base-layer claims.

## What would be needed to promote it

Promote this into a vulnerability example only if historical evidence shows a
distinct defect not visible in the high-level mapping, such as:

- a failing CPU/GPU claim-parity vector at the earlier revision;
- a CUB or iterator defect triggered by the production dimensions;
- an asynchronous lifetime or scratch-buffer hazard;
- a field-type-specific segmented-reduction failure; or
- a completed proof rejected because these exact claims were wrong.

That evidence must identify the triggering configuration and connect the bad
reduction output to a proof consumer. Until then this file is useful as an
example of the evidence gate: commit labels and plausible accelerator folklore
must not be converted into a fabricated vulnerability mechanism.

## Reproduction evidence

```sh
git diff 41464ee88a9bbe40c11a5e296e505e9f09fb90b3 6beb5fccc168f539f073426f3b4f2199b4b18e3b -- gpu_prover/src/prover/gkr/base_layer_claims.rs
git show 41464ee88a9bbe40c11a5e296e505e9f09fb90b3:gpu_prover/src/ops/cub/device_reduce.rs
git show 41464ee88a9bbe40c11a5e296e505e9f09fb90b3:gpu_prover/native/ops/cub/device_reduce.cu
```
