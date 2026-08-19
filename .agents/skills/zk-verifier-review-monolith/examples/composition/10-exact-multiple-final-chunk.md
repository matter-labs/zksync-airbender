# Exact-multiple replay dropped the final full chunk

## Classification

- Confirmed historical proving completeness bug
- Fixed by: [`0a918ce`](https://github.com/matter-labs/zksync-airbender/commit/0a918ceb9c10279505cf4e5b3cb611fba2f335e4), PR [#325](https://github.com/matter-labs/zksync-airbender/pull/325)
- Vulnerable revision: `b566d65ce9b1f9b7ee9cae6d4325adc5528f38c0`

## Failure

Three replay helpers sized the last chunk as `num_calls % capacity`. For any positive exact multiple, the final chunk was full but received length zero, was truncated, and triggered the coverage assertion.

## Impact and fix

Attacker-influenced programs with exact-capacity family/delegation counts could not be proven. The fix maps zero remainder to a full final chunk after the existing zero-call early return.

## Regression

Cover partial counts and `k * capacity` for several `k`, asserting total reconstructed events equals input calls.

```sh
git diff b566d65ce9b1f9b7ee9cae6d4325adc5528f38c0 0a918ceb9c10279505cf4e5b3cb611fba2f335e4 -- prover/src/witness_evaluator/unrolled/mod.rs
```
