# Unified GPU permutation lost the prior accumulator

## Classification

- Confirmed historical global permutation implementation bug
- Fixed by: [`361e73f`](https://github.com/matter-labs/zksync-airbender/commit/361e73f7d55ef3f630b13bb1b8c90992ce30e913), PR [#167](https://github.com/matter-labs/zksync-airbender/pull/167)
- Vulnerable revision: `967362b4a3920b64e484ab62260cde096068da1a`

## Failure

The unified stage-3 CUDA path processed machine-state masking and then shuffle-RAM initialization without marking the preceding argument value initialized or carrying `e4_arg` into `e4_arg_prev`.

## Impact and fix

The next grand-product recurrence started from the wrong predecessor, so the unified global permutation contribution differed from the canonical prover/verifier relation. The fix explicitly carries the prior accumulator for this combined corner case.

## Regression

Compare CPU/GPU grand-product columns and final accumulator for unified circuits with machine-state masking plus more than one init/teardown set.

```sh
git diff 967362b4a3920b64e484ab62260cde096068da1a 361e73f7d55ef3f630b13bb1b8c90992ce30e913 -- gpu_prover/native/stage3.cu gpu_prover/src/prover/stage_3_kernels.rs
```
