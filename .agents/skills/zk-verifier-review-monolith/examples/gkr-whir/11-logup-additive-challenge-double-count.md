# Unbalanced LogUp kernel added gamma twice

## Classification

- Confirmed historical protocol-specific Sumcheck gate bug
- Component: quadratic-only kernel for an unbalanced rational lookup relation
- Claim-chain location: LogUp pair gate → Sumcheck round polynomial → terminal lookup output
- Security character: prover/canonical gate mismatch; shared verifier logic would enforce the wrong rational identity
- Fixed by: [`a1ae551`](https://github.com/matter-labs/zksync-airbender/commit/a1ae551a9ccfa8f6860d4aec845a16030d02364c)
- Vulnerable revision: `06c4fc94cbc71d5132afe24c9f77695756595670`

## Protocol context

LogUp represents lookup sums as numerator/denominator pairs and aggregates them through GKR. The affected unbalanced relation combined an existing rational pair with one base-input denominator. By the time the quadratic-only kernel receives base value `d`, the additive lookup challenge `γ` has already been incorporated according to the forward relation's input contract.

The optimized Sumcheck kernel must evaluate the same cleared-denominator polynomial as forward witness construction and the verifier's terminal gate. Challenge injection belongs at exactly one layer.

## Intended gate relation

Conceptually, for the relation combining `a/b` with an additional shifted denominator:

```text
d = materialized denominator supplied by the relation input contract
quadratic products use a*d and b*d
do not replace d by d + γ again inside the optimized kernel
```

The exact numerator addition is handled by the surrounding relation representation; the important invariant is that the same `d` reaches full and quadratic-only evaluation.

## Failure

`pointwise_eval_quadratic_only_impl` accepted `lookup_additive_challenge` and called `d.add_with_ext(γ)` before multiplying. Because `d` already represented the shifted/materialized denominator, the optimized path evaluated a relation with `d + γ`—effectively adding the challenge twice—while the forward gate used `d`.

The function signature itself encouraged the bug by exposing a challenge that the kernel should not own.

## Failure flow

1. Draw lookup additive challenge `γ` and construct the relation's base denominator input.
2. Forward evaluation and stored GKR values use that materialized `d`.
3. Sumcheck's quadratic-only kernel adds `γ` again.
4. Round coefficients encode products with `d + γ`.
5. Terminal gate evaluation uses products with `d`.
6. Honest proof fails the final Sumcheck pin or self-check.

An accepting verifier sharing the duplicate addition would prove a different lookup identity. The historical location is prover-side, so deployed severity requires generated-verifier reachability.

## Impact and fix

The Sumcheck polynomial no longer represented the LogUp gate whose outputs were being claimed. The fix removes the challenge parameter from the helper and multiplies directly by `d`, making duplicate injection impossible at that call boundary.

Track challenge ownership through typed dataflow. A value named `denominator` should state whether it is raw, RLC-compressed, gamma-shifted, inverted, or materialized; otherwise optimizations easily apply transformations twice.

## Regression

- Compare full pointwise and quadratic-only evaluations over several `γ`, including zero and nonzero values.
- Use direct cleared-denominator rational algebra as an independent oracle.
- Vary `d`, numerator/denominator pair values, and exceptional zero denominators.
- Assert the additive challenge is introduced exactly once in the relation's call graph.
- Check prover kernel and generated verifier terminal gate from the same test vector.

## Reproduction evidence

```sh
git diff 06c4fc94cbc71d5132afe24c9f77695756595670 a1ae551a9ccfa8f6860d4aec845a16030d02364c -- prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/lookup_rational_with_unbalanced_base.rs
```
