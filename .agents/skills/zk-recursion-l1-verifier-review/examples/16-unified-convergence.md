# Unified recursion did not enforce terminal convergence

## Classification

- Confirmed historical terminal-statement soundness bug
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Failure

Unified verification accepted any proof valid in that recursion layer without checking that its family-proof count had reached the terminal shape required by the selected security level.

## Impact and fix

A partially compressed intermediate artifact could be accepted as the final settlement artifact; security 100 in particular requires two-step convergence. The fix checks the family count with the trusted security-level model before accepting the unified target.

## Regression

For every supported security level, reject each pre-terminal family count and accept only the declared converged count; require a rule when adding a level.

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/prover_utils.rs
```
