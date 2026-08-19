# Recursive proof output was not bound to the supplied program

## Classification

- Confirmed historical recursion-anchoring soundness bug
- Fixed by: [`a2d7ad1`](https://github.com/matter-labs/zksync-airbender/commit/a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0), PR [#321](https://github.com/matter-labs/zksync-airbender/pull/321)
- Vulnerable revision: `180c1c336e4c939e57a54559e0d507e8ef359745`

## Failure

CLI verification checked editable artifact metadata and a program-independent recursion-verifier setup, but discarded the authenticated recursion chain returned in `output[8..16]`. It never compared that chain with the one derived from the supplied program.

## Impact and fix

A valid recursive proof for program Q could be relabeled and accepted for program P. The fix compares the verifier-derived output chain with the correct program-derived chain in every base, unrolled, and unified target branch.

## Regression

Verify one proof against its real program, then rewrite only metadata and attempt verification against a distinct program with the same recursion verifier.

```sh
git diff 180c1c336e4c939e57a54559e0d507e8ef359745 a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0 -- tools/cli/src/prover_utils.rs
```
