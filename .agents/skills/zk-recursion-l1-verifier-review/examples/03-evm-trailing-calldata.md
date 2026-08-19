# WHIR contract accepted trailing proof calldata

## Classification

- Confirmed historical L1 proof-parser malleability bug
- Fixed by: [`4b0d431`](https://github.com/matter-labs/zksync-airbender/commit/4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8)
- Vulnerable revision: `585e7c9384f83e2d6b98023d8aa5bdd001686faa`

## Failure

After the final WHIR query, the contract did not require its calldata cursor to equal `calldatasize()`. Appended bytes were silently ignored while the registry was notified of success.

## Impact and fix

Multiple byte encodings represented the same accepted proof, complicating proof identity, relayer authorization, and recursive handoff assumptions. The fix requires exact proof-stream consumption.

## Regression

Append 1, 16, and 32 bytes to a valid proof and require revert; separately cover intentional framing bytes at the GKR-to-WHIR boundary.

```sh
git diff 585e7c9384f83e2d6b98023d8aa5bdd001686faa 4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8 -- verifier_evm/src/templates/whir.sol
```
