# Generated EVM verifier hardcoded layer count and output order

## Classification

- Confirmed historical generated-artifact drift bug
- Fixed by: [`5459c07`](https://github.com/matter-labs/zksync-airbender/commit/5459c07f94f5b6c843c0cb405ee797a4b2e93e7f)
- Vulnerable revision: `1500f8ba394ecc320955493ac12d4030ffd20271`

## Failure

The EVM driver hardcoded which `sumcheck_circuit_layer{i}` functions to call and the boundary LSB reorder. Circuit depth and GKR-address order changed independently of those literals.

## Impact and fix

Generated contracts could omit a layer, call stale functions, or place memory/lookup outputs in the wrong logical accumulator slots. The fix derives reverse layer calls and output permutation from the `GKRCircuitArtifact` and asserts template markers.

## Regression

Regenerate after adding/removing a layer and permuting output addresses; compare the contract's call graph and boundary map to the artifact.

```sh
git diff 1500f8ba394ecc320955493ac12d4030ffd20271 5459c07f94f5b6c843c0cb405ee797a4b2e93e7f -- verifier_evm/src/generator/circuit_yul.rs
```
