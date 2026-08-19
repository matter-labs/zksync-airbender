# Zero-width base cap changed the GPU transcript

## Classification

- Confirmed historical optional/empty-message transcript bug
- Component: GKR base commitments and WHIR proof parsing
- Fixed by: [`6bd4fdf`](https://github.com/matter-labs/zksync-airbender/commit/6bd4fdf42071903e8f3033b472ee20aee7bab180)
- Vulnerable revision: `eac16fe5cf56dfdda86d44beccf2597a97b70cd6`

## Failure

For the width-zero witness layer of inits/teardowns, GPU code absorbed a dummy cap that the CPU/verifier omitted and later serialized a 16-digest degenerate cap instead of an empty cap.

## Impact and fix

Every downstream challenge diverged only on this empty-layer path. The fix gates cap absorption and parsing on the declared column width. Optional and zero-length protocol messages require explicit, identical rules in every implementation.

## Regression

Run byte-exact proof and transcript parity for widths 0, 1, and a normal multi-column layer.

```sh
git diff eac16fe5cf56dfdda86d44beccf2597a97b70cd6 6bd4fdf42071903e8f3033b472ee20aee7bab180 -- gpu/circuit_prover/src/prover/proof/orchestration/stage1_forward.rs gpu/circuit_prover/src/prover/proof_layout/accessors.rs
```
