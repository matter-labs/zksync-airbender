# Unified GPU permutation lost the prior accumulator

## Classification

- Confirmed historical global permutation implementation bug
- Invariant: each argument segment starts from the terminal accumulator of the immediately preceding segment
- Component: unified stage-3 CUDA grand-product construction
- Security character: GPU/canonical relation mismatch in a combined machine-state-mask plus shuffle-RAM path
- Fixed by: [`361e73f`](https://github.com/matter-labs/zksync-airbender/commit/361e73f7d55ef3f630b13bb1b8c90992ce30e913), PR [#167](https://github.com/matter-labs/zksync-airbender/pull/167)
- Vulnerable revision: `967362b4a3920b64e484ab62260cde096068da1a`

## Composition context

The GPU constructs grand-product columns for several argument segments in one stage. The accumulator recurrence crosses segment boundaries: a later shuffle-RAM initialization must receive the final extension-field accumulator from the prior machine-state masking segment when both are present.

Implementation metadata tracks whether a predecessor is initialized and stores `e4_arg_prev`. Those fields encode an algebraic edge, not merely kernel scheduling state.

## Intended invariant

If segment `B` follows nonempty segment `A`:

```text
arg_prev_is_initialized = true
e4_arg_prev = terminal_accumulator(A)
first_accumulator(B) = recurrence(e4_arg_prev, first_factor(B))
```

If no prior segment exists, only then may `B` begin from the protocol identity. CPU and GPU must agree on segment order and identity conventions.

## Failure

The unified CUDA path processed machine-state masking and then shuffle-RAM initialization but did not set `arg_prev_is_initialized` or carry the current `e4_arg` into `e4_arg_prev`. The next recurrence therefore behaved as if no prior argument segment existed.

Each segment's local factors could be correct while the concatenated product column was wrong at exactly one handoff. Final-accumulator-only debugging obscures this because the mismatch appears after many otherwise valid multiplications.

## Failure flow

1. Enable unified machine-state masking and multiple init/teardown/shuffle-RAM sets.
2. Compute the terminal machine-state accumulator correctly.
3. Enter shuffle-RAM initialization with predecessor metadata still unset.
4. Initialize from identity/stale state instead of the machine-state terminal value.
5. Produce a grand-product column and output contribution different from the canonical prover/verifier relation.

The historical path causes honest GPU proof failure. If analogous state loss occurred in a verifier-side aggregation routine, it could omit an entire participant segment, so the same handoff audit applies at every implementation boundary.

## Impact and fix

Unified GPU permutation columns and final contribution diverged only in the combined corner case. The fix explicitly marks the predecessor initialized and assigns the current extension-field accumulator before starting the following segment. A related Rust-side assertion was relaxed for the unified one-set layout to match valid geometry.

Composition audits should expand every accumulator into a participant sequence and check the recurrence at boundaries. A product-of-products is only equivalent to one global product if no transition resets, duplicates, or skips the carried value.

## Regression

- Compare CPU/GPU grand-product columns at every segment boundary, not only the terminal value.
- Exercise all presence combinations: neither segment, each alone, and both together.
- Cover one and multiple init/teardown sets in unified mode.
- Seed the prior accumulator with a non-identity value so accidental reset is observable.
- Assert the outer verifier's final contribution matches the same participant order.

## Reproduction evidence

```sh
git diff 967362b4a3920b64e484ab62260cde096068da1a 361e73f7d55ef3f630b13bb1b8c90992ce30e913 -- gpu_prover/native/stage3.cu gpu_prover/src/prover/stage_3_kernels.rs
```
