# GPU query draw advanced one digest too far

## Classification

- Confirmed historical Fiat-Shamir squeeze-length mismatch
- Component: WHIR query-index drawing
- Fixed by: [`c1e0576`](https://github.com/matter-labs/zksync-airbender/commit/c1e0576ec77ded9a2436dfe74475d97986527d94)
- Vulnerable revision: `1b653f86adf8f6d2e12cba664f7ce10f085d381`

## Failure

The GPU counted the PoW header word once in `total_bits` and again in the padded word count. At digest-block boundaries it squeezed 16 words where the CPU/verifier squeezed 8. Query indices used only the common prefix and matched; the rolling seed did not.

## Impact and fix

The first visible failure occurred at the next delinearization challenge, far from the cause. The fix computes words from query bits alone and adds the skipped header exactly once. Transcript audits must compare state advancement, not merely extracted values.

## Regression

Test bit counts on both sides of every digest-block boundary and compare the next challenge as well as query indices.

```sh
git diff 1b653f86adf8f6d2e12cba664f7ce10f085d381 c1e0576ec77ded9a2436dfe74475d97986527d94 -- gpu/circuit_prover/src/prover/pow.rs
```
