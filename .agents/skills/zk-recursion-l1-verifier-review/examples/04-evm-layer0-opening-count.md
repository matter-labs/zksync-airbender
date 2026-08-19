# EVM layer-0 opening list stopped at 72 instead of 113

## Classification

- Confirmed historical L1 GKR verification bug
- Fixed by: [`16a5ceb`](https://github.com/matter-labs/zksync-airbender/commit/16a5cebf46a3ffa378a4dc893a302d33a359d9d7)
- Vulnerable revision: `fe19aa23dce1c5bdac100756cc2a51f15f6af29e`

## Failure

The generated layer-0 verifier consumed and transcript-batched 72 point claims even though the current artifact exposed 113. Its parser also derived the base input width from the wrong group accounting.

## Impact and fix

Forty-one prover-supplied base openings were outside the layer-0 claim batch, and subsequent calldata parsing began at the wrong offset. The fix updates the count, transcript helper, pointer advance, and generator width assertion.

## Regression

Derive opening count from the artifact, assert exact cursor movement, and mutate the first and last opening independently.

```sh
git diff fe19aa23dce1c5bdac100756cc2a51f15f6af29e 16a5cebf46a3ffa378a4dc893a302d33a359d9d7 -- verifier_evm/circuit.yul verifier_evm/parse.rs
```
