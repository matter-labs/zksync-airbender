# Empty ABI high limbs were read as real columns

## Classification

- Confirmed historical generated-verifier completeness/correctness bug
- Fixed by: [`613c8de`](https://github.com/matter-labs/zksync-airbender/commit/613c8de2c215d498a0646c2c883f029f49fae6e8)
- Vulnerable revision: `23f5b8bf72b6ab68f4589a5db45561cda7974727`

## Failure

Delegation quotient generation unconditionally read `abi_mem_offset_high.start()` even when the optional column range was empty. In such layouts the absent high limb semantically equals zero.

## Impact and fix

The verifier read a neighboring/unrelated opening or generated unusable code for a valid circuit layout. The fix branches on `num_elements()` and emits field zero for the empty range.

## Regression

Generate and verify otherwise identical layouts with zero and one ABI-high column; inspect all optional range accesses for a zero-width branch.

```sh
git diff 23f5b8bf72b6ab68f4589a5db45561cda7974727 613c8de2c215d498a0646c2c883f029f49fae6e8 -- verifier_generator/src/inlining_generator/everywhere_except_last.rs
```
