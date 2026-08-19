# Keccak recursion boundary timestamp was one cycle late

## Classification

- Confirmed historical recursive public-state bug
- Fixed by: [`93e124e`](https://github.com/matter-labs/zksync-airbender/commit/93e124e704bd330795288ab9800db41c495a0441)
- Vulnerable revision: `38baa31aec8ed87041c5fcc98bd9b8c15a563434`

## Failure

The Keccak delegation VM placed final x10/x11 timestamps at `entry + NUM_CALLS * TIMESTAMP_STEP + 3`, while the last internal call is numbered `NUM_CALLS - 1` and the outer cycle performs the final default increment.

## Impact and fix

The public register state carried into recursion was one cycle later than replay and memory events, breaking chain continuity. The fix uses `(NUM_CALLS - 1) * TIMESTAMP_STEP + 3`.

## Regression

Compare VM, replayer, circuit output, and recursion public state for the first and final Keccak delegation cycles.

```sh
git diff 38baa31aec8ed87041c5fcc98bd9b8c15a563434 93e124e704bd330795288ab9800db41c495a0441 -- riscv_transpiler/src/vm/delegations/keccak_special5.rs
```
