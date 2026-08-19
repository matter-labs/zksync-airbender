# EVM verifier omitted all LogUp identity checks

## Classification

- Confirmed historical L1 verifier soundness bug
- Fixed by: [`bf9bd04`](https://github.com/matter-labs/zksync-airbender/commit/bf9bd04f2ac916eb8e65603cdba72f563b98351f)
- Vulnerable revision: `33f2685b8e602eec323c4e470729db09e433f060`

## Failure

The GKR contract checked the memory permutation identity but never checked the three LogUp output pairs. Prover-supplied boundary numerators and denominators were parsed and used in GKR without requiring each rational sum to equal zero or denominators to be nonzero.

## Impact and fix

An on-chain proof could satisfy layer reductions while its lookup arguments remained globally inconsistent. The fix accumulates each pair as one fraction, requires zero numerator and nonzero denominator, and calls the checks before proof exhaustion.

## Regression

Mutate each lookup pair independently, including a zero denominator, while leaving the GKR transcript structurally valid.

```sh
git diff 33f2685b8e602eec323c4e470729db09e433f060 bf9bd04f2ac916eb8e65603cdba72f563b98351f -- verifier_evm/src/templates/gkr.sol
```
