# MaxQuadratic reused terms and polluted the quadratic coefficient

## Classification

- Confirmed historical Sumcheck polynomial-construction bug
- Component: optimized `MaxQuadratic` evaluation kernel
- Claim-chain location: gate polynomial → round univariate coefficients
- Security character: prover/canonical-verifier incompleteness; an accepting verifier sharing the kernel would check the wrong gate polynomial
- Fixed by: [`a514b2d`](https://github.com/matter-labs/zksync-airbender/commit/a514b2d3bf4a19a8725baa721ce8f7f32a7259f1)
- Vulnerable revision: `d04ee655d3bb20e43786f7316416714ea0f032cb`

## Protocol context

A `MaxQuadratic` relation represents a constant, linear terms, and groups of independent quadratic monomials. During Sumcheck the optimized kernel accumulates the coefficients of the univariate round polynomial obtained by restricting all earlier variables and leaving the current Boolean variable symbolic.

Two invariants matter independently: every stored `(a, b, coefficient)` describes one monomial starting from the same `input[a]`, and the coefficient accumulator for degree two contains only terms that actually vary quadratically. A constant offset contributes to the degree-zero coefficient, never degree two.

## Intended claim relation

For the selected round polynomial `g(X)`:

```text
g(X) = constant
     + Σ linear_term_i(X)
     + Σ independent_quadratic_term_j(X)

g(0) + g(1) = incoming_sumcheck_claim
outgoing_claim = g(r)
terminal_claim = batched_gate_evaluation(folded_inputs)
```

The optimized coefficient path must agree with direct pointwise evaluation/interpolation for every `X`, not merely at Boolean endpoints.

## Failure

`MaxQuadratic` initialized one mutable `contribution` outside the inner `(b, coeff)` loop. After computing the first monomial for a fixed `a`, the next monomial started from the previous product rather than from `input[a]`. Terms that should have been added independently therefore compounded and could acquire extra factors.

The first-round quadratic-coefficient path also initialized its accumulator from `constant_offset`. That inserted a degree-zero value into the degree-two slot. These are separate coefficient errors in the same optimized relation.

## Failure flow

1. Use at least two quadratic terms sharing the same outer address `a`.
2. The first term evaluates from `input[a]` as intended.
3. The second term reuses that result and multiplies/scales it again, producing a different monomial and potentially a higher effective degree.
4. Add the constant offset to the quadratic coefficient in the specialized first round.
5. Emit a round polynomial that does not represent the claimed gate relation.
6. A canonical verifier eventually rejects at a round identity or final gate pin; self-checks caught this in historical tests.

No false acceptance by an independent correct verifier follows from a wrong honest-prover polynomial. The soundness concern arises only if a verifier or generated checker reuses the same faulty coefficient construction.

## Impact and fix

Honest Sumcheck claims could diverge from the actual batched gate polynomial, with failures depending on term grouping and nonzero constants. The fix resets `contribution` from `input[a]` inside every monomial iteration and starts the quadratic-only accumulator from field zero.

Optimized relation kernels must be treated as alternate theorem implementations. Validate each coefficient slot against a specification-level evaluator and test degrees, not just final proof acceptance.

## Regression

- Compare optimized coefficients with direct evaluation/interpolation over several random points.
- Include two or more terms sharing `a`, asymmetric `a != b` terms, repeated/diagonal terms, and nonzero constants.
- Check every coefficient slot separately, especially the highest-degree slot.
- Run the same relation through prover self-checks and the generated verifier's terminal gate evaluation.
- Add a degree assertion so accidental term compounding cannot silently exceed the declared Sumcheck degree.

## Reproduction evidence

```sh
git diff d04ee655d3bb20e43786f7316416714ea0f032cb a514b2d3bf4a19a8725baa721ce8f7f32a7259f1 -- prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/max_quadratic_rel.rs
```
