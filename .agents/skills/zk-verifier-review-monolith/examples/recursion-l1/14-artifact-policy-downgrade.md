# Verification policy came from prover-controlled metadata

## Classification

- Confirmed historical verifier-policy soundness bug
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Failure

`verify` and parts of `continue-proof` selected `security_level`, target, recursion binaries, and verification flow from fields inside the proof artifact. Those fields are prover-controlled metadata, not verifier policy.

## Impact and fix

An artifact could steer acceptance into a weaker security schedule or a different stage than the caller requested. The fix requires trusted command-line policy, selects the flow from it, and rejects artifacts whose metadata disagrees.

## Regression

Present artifacts whose target and security level independently disagree with trusted caller inputs; assert rejection before binary or protocol selection.

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/main.rs tools/cli/src/prover_utils.rs
```
