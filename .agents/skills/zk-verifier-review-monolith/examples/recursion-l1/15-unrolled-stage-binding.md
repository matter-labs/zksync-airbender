# Unrolled recursion was not bound to the wrapped stage

## Classification

- Confirmed historical recursion-stage soundness bug
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Failure

A `recursion-unrolled` artifact's chain was checked for internal validity and program identity, but not against the expected unrolled-recursion stage. Under the accepted shape, an authenticated base-layer chain could stand in for an unrolled chain.

## Impact and fix

The consumer could accept a proof as one recursion layer deeper than the chain actually attested. The fix requires the authenticated output to equal the supplied program's unrolled-stage chain regardless of whether the wrapper consumed base or prior-unrolled input.

## Regression

Construct the target/source-stage matrix and prove that a base chain is rejected for an unrolled target while the exact unrolled chain is accepted.

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/prover_utils.rs
```
