# Yul cached gate values were not reduced modulo the field

## Classification

- Confirmed historical EVM field-representation bug
- Fixed by: [`fe19aa2`](https://github.com/matter-labs/zksync-airbender/commit/fe19aa23dce1c5bdac100756cc2a51f15f6af29e)
- Vulnerable revision: `a2e18444359b6f5c93845f9d15c9445290c68503`

## Failure

Generated Yul stored raw gate expressions in `GKR_CIRCUIT_CACHE_PTR`. Add/sub expressions could exceed the Proth field modulus; later consumers treated cache slots as canonical field elements while multiplication paths used modular arithmetic.

## Impact and fix

Equivalent field values could compare differently or feed inconsistent later gate evaluations. The fix stores `mod(gate, P)` and hardens negative-term generation and missing constraints.

## Regression

Drive cache expressions above `P` and `2P`, then compare all cached and uncached gate paths to Rust field evaluation.

```sh
git diff a2e18444359b6f5c93845f9d15c9445290c68503 fe19aa23dce1c5bdac100756cc2a51f15f6af29e -- verifier_evm/circuit.yul verifier_evm/gkr.sol verifier_evm/parse.rs
```
