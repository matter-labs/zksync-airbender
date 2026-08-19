# Replay early return skipped the timestamp increment

## Classification

- Confirmed historical machine-state continuity bug
- Fixed by: [`6538ff5`](https://github.com/matter-labs/zksync-airbender/commit/6538ff5a4c58ace853d9c6b7eadc4199579d1097)
- Vulnerable revision: `e30029fb28b99e2146652c746d2ece6fd4953919`

## Failure

The replayer checked whether PC had reached the stop point and returned before applying `TIMESTAMP_STEP`. The terminal cycle therefore consumed no timestamp even though the circuit execution did.

## Impact and fix

Final PC/timestamp state and memory access times diverged between replay and proof construction, breaking cross-chunk continuity. The fix increments first, then tests the stop condition.

## Regression

Test one-cycle and multi-cycle replay where the terminal instruction leaves PC unchanged; compare final timestamps to the circuit trace.

```sh
git diff e30029fb28b99e2146652c746d2ece6fd4953919 6538ff5a4c58ace853d9c6b7eadc4199579d1097 -- riscv_transpiler/src/replayer/mod.rs
```
