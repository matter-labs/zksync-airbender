# Unbalanced LogUp corrupted the quadratic coefficient and extension addition

## Classification

- Producer-parity history: confirmed historical protocol-specific Sumcheck kernel defects in a pre-assembly prover
- Component: quadratic-only kernel for an unbalanced rational lookup relation
- Claim-chain location: LogUp pair gate → Sumcheck round polynomial → terminal lookup output
- Security character: latent; the enclosing GKR prover still ended in an unconditional `todo!()` and could not emit a proof
- Fixed by: [`a1ae551`](https://github.com/matter-labs/zksync-airbender/commit/a1ae551a9ccfa8f6860d4aec845a16030d02364c)
- Vulnerable revision: `06c4fc94cbc71d5132afe24c9f77695756595670`
- Activation condition: completing `prove_configured_with_gkr` or otherwise exposing this relation through a proof-producing entrypoint

## Protocol context

LogUp represents lookup sums as numerator/denominator pairs and aggregates them through GKR. The affected unbalanced relation combined an existing rational pair with one base input shifted by the lookup challenge. Its full pointwise relation uses `d + γ`; the specialized quadratic-only path computes only the highest-degree contribution of that relation to a Sumcheck round polynomial.

The optimized Sumcheck kernel must agree coefficient-by-coefficient with the same cleared-denominator polynomial as forward witness construction and the terminal gate. A constant shift can affect lower coefficients while disappearing from the homogeneous quadratic coefficient.

## Intended gate relation

For the relation combining `a/b` with `1/(d + γ)`, the cleared outputs are:

```text
full numerator   = a*(d + γ) + b
full denominator = b*(d + γ)

quadratic-only numerator coefficient   = a*d
quadratic-only denominator coefficient = b*d
```

The `γ*a`, `γ*b`, and standalone `b` terms are lower degree in the folding variable and must not be inserted into the quadratic-only coefficient.

## Failure

`pointwise_eval_quadratic_only_impl` called `d.add_with_ext(γ)` and then multiplied by `a` and `b`. Even with a correct addition helper, this incorrectly inserted the constant-shift terms into the quadratic coefficient.

The same fix also corrected a separate generic defect: `ExtensionFieldRepresentation::add_with_ext` performed `self.value *= other` rather than addition. Full pointwise evaluation using an extension representation therefore computed `d*γ` where its API promised `d+γ`. The historical patch both removed `γ` from the quadratic-only helper and changed `add_with_ext` from multiplication to addition.

## Failure flow

1. Draw lookup additive challenge `γ` and evaluate the full relation using `d + γ`.
2. Enter a Sumcheck path that asks only for the quadratic coefficient.
3. The optimized helper includes `γ` even though a constant shift contributes only to lower-degree slots.
4. If the representation is already extension-valued, the misimplemented helper multiplies by `γ` instead of adding it.
5. The emitted round coefficients differ from interpolation of the full gate polynomial.
6. A completed prover would fail a Sumcheck identity, final gate pin, or independent self-check.

At the vulnerable revision the enclosing prover still terminated with `todo!()`, so no proof reached a verifier and this remains latent. A future accepting verifier that copied either faulty coefficient rule would check a different polynomial from the intended LogUp relation.

## Impact and fix

The Sumcheck polynomial did not represent the LogUp gate whose outputs were being claimed. The fix removes the challenge parameter from the quadratic-only helper, multiplies directly by `d`, and restores addition semantics for the extension representation.

Track both challenge ownership and coefficient degree through typed dataflow. A value named `denominator` should state whether it is raw, shifted, inverted, or materialized, while an optimized helper should state which homogeneous coefficient it computes.

## Regression

- Interpolate the full pointwise relation and compare every coefficient with the optimized path over several `γ`.
- Use direct cleared-denominator rational algebra as an independent oracle.
- Vary `d`, numerator/denominator pair values, and exceptional zero denominators.
- Unit-test `add_with_ext` for base, collapsed, and extension representations so it cannot alias multiplication.
- Assert the additive challenge is absent from the homogeneous quadratic-only helper.
- Check prover kernel and generated verifier terminal gate from the same test vector.

## Reproduction evidence

```sh
git diff 06c4fc94cbc71d5132afe24c9f77695756595670 a1ae551a9ccfa8f6860d4aec845a16030d02364c -- prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/lookup_rational_with_unbalanced_base.rs prover/src/gkr/sumcheck/evaluation_kernels/mod.rs
```
