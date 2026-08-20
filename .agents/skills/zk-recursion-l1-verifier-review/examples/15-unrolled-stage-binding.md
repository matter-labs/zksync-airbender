# Unrolled recursion was not bound to the wrapped stage

## Classification

- Confirmed historical recursion-stage soundness bug
- Boundary: authenticated recursion-chain output → claim that an artifact reached `RecursionUnrolled`
- Component: unrolled target verification over either base or prior-unrolled inputs
- Security character: stage/type confusion inside an otherwise valid recursive chain
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Boundary context

Program identity alone is not enough to describe a recursive artifact. Each recursion stage has its own expected authenticated hash chain. A proof can validly attest to the correct program at the base stage while still failing the caller's requirement that it has been wrapped by the unrolled-recursion program.

The unrolled verifier may accept two legitimate input shapes—directly over base or over a previous unrolled proof—but its output must identify the unrolled stage in both branches:

```text
source in {base, prior_unrolled}
target = unrolled
require authenticated_output_chain == program.unrolled_level.hash_chain
```

## Failure

A `recursion-unrolled` artifact's chain was checked for internal validity and program identity, but one target branch compared it with the base-level expectation rather than requiring the unrolled-level chain. Under the accepted proof shape, an authenticated base-stage chain could therefore satisfy a wrapper claim labeled as unrolled.

## Adversarial flow

1. Obtain a valid authenticated chain for the target program at the base stage.
2. Place it in an artifact/shape routed through `RecursionUnrolled` verification.
3. The recursive proof and program identity checks succeed.
4. The wrapper compares the authenticated output with the base-stage chain or omits the unrolled-stage equality.
5. The artifact is accepted as one stage deeper than the chain it attests.

This is a boundary type-confusion bug: “same program” was used as a proxy for “same program and required recursion stage.”

## Impact and fix

The consumer could accept a proof as one recursion layer deeper than the chain actually attested. The fix centralizes an unrolled-target check requiring authenticated output to equal the supplied program's `unrolled_level.hash_chain`, regardless of whether the wrapper consumed base or prior-unrolled input.

Stage tags in JSON do not repair this issue: they are untrusted. The stage must be derived from authenticated output and compared with trusted target policy.

## Regression

- Construct the complete source-stage × target-stage matrix.
- Require a base chain to fail for an unrolled target even when program identity and proof shape are otherwise valid.
- Accept the exact unrolled chain for both permitted source shapes.
- Mutate one authenticated chain limb at a time and ensure no metadata copy controls the result.
- Ensure every new recursion stage defines a distinct expected chain and terminal consumer rule.

## Reproduction evidence

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/prover_utils.rs
```
