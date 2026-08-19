# Padding rows used PC zero instead of PC_STEP

## Classification

- Confirmed historical padding-state bug
- Fixed by: [`e5815c5`](https://github.com/matter-labs/zksync-airbender/commit/e5815c54f8a185592fb4a190cd7b7f6a3927d782)
- Vulnerable revision: `dad06de77cfa01d2734a7b39c9113de480a3bc17`

## Failure

GPU `jump_branch_slt` padding rows used a stale PC value of zero while CPU setups used `PC_STEP = 4`. The memory commitment therefore encoded different final-PC state on padding.

## Impact and fix

Padding contaminated a globally composed state column, changed the Merkle cap and all later challenges, and broke proof parity. The fix references the shared constant rather than a literal.

## Regression

For every circuit family, compare CPU/GPU padding rows and assert padding contributes the specified neutral global state.

```sh
git diff dad06de77cfa01d2734a7b39c9113de480a3bc17 e5815c54f8a185592fb4a190cd7b7f6a3927d782 -- gpu/circuit_prover/src/witness/circuit_type.rs
```
