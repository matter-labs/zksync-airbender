# Unified GPU permutation could not hand off the prior accumulator

## Classification

- Producer-parity history: confirmed historical global permutation implementation bug
- Invariant: each argument segment starts from the terminal accumulator of the immediately preceding segment
- Component: unified stage-3 Rust metadata and CUDA grand-product handoff
- Security character: confirmed fail-closed honest-proof/completeness failure;
  the underlying CUDA handoff would also be wrong if the guard alone were
  relaxed
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

The vulnerable implementation had two matching defects at the same handoff:

1. Rust static-metadata construction asserted that an unrolled circuit with
   any init/teardown set could not already have an initialized permutation
   accumulator. The unified circuit is the counterexample: it has a prior
   machine-state/mask segment and exactly one following init/teardown set, so
   public GPU proof construction failed closed at this assertion.
2. The CUDA path after machine-state masking did not set
   `arg_prev_is_initialized` or copy `e4_arg` into `e4_arg_prev`. If the Rust
   guard were merely relaxed, shuffle-RAM initialization would start from
   identity/stale state instead of the prior segment's terminal accumulator.

Thus the historical active impact was an honest proving failure, not an
accepted malformed product. The kernel defect explains why removing only the
guard would have been an incorrect repair.

## Failure flow

1. Supply the repository's unified compiled circuit to the public
   `gpu_prover::prover::proof::prove` path.
2. Static metadata observes a prior machine-state accumulator and one
   init/teardown set.
3. The stale assertion requires the prior accumulator to be absent and panics,
   so no proof is produced.
4. Under a guard-only patch, CUDA would instead enter shuffle-RAM initialization
   with predecessor metadata unset and construct the wrong product from
   identity/stale state.

The canonical CPU relation and verifier retain the prior product. No historical
false acceptance follows because the vulnerable Rust path stopped before
producing that malformed proof.

## Impact and fix

Unified GPU proof construction failed in the combined corner case. The fix
narrows the Rust assertion so the valid unified one-set layout proceeds, then
explicitly marks the predecessor initialized and carries the current
extension-field accumulator before starting the following segment.

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
git show 967362b4a3920b64e484ab62260cde096068da1a:gpu_prover/src/prover/proof.rs
```
