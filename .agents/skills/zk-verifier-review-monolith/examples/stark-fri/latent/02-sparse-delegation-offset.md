# Sparse delegation quotient scaled the address itself

## Classification

- Confirmed historical generated-quotient relation defect in an un-emitted branch
- Component: delegation RAM tuple evaluation for variable-dependent sparse access
- Reduction location: address derivation → memory compression → grand-product quotient
- Security character: latent; no checked-in vulnerable verifier contained the expression, and the affected sparse layout failed artifact compilation for the separate Option-serialization defect
- Fixed by: [`9b955b6`](https://github.com/matter-labs/zksync-airbender/commit/9b955b649cfbd1ef04305ec15af344dc5a41354f)
- Vulnerable revision: `6327a202048659bd8afac3b65cf65bb7e2ed9fc3`
- Activation condition: successfully emit and compile a verifier for a variable-dependent sparse indirect access while retaining the wrong affine-expression branch

## Protocol context

Sparse delegation accesses derive a RAM address from a base/register value, a constant offset, and an optional variable offset with a small coefficient. The resulting address limbs enter the randomized memory tuple and grand-product relation verified through the quotient.

For a variable-dependent access the intended low limb is:

```text
address_low = base_address_low + constant_offset + coefficient * variable_offset
```

Carry handling is a separate path. The affected branch had no carry-bit column and generated the affine expression inline.

## Intended quotient relation

The verifier must compute the exact address used by witness/circuit semantics before compression:

```text
variable_contribution = coefficient * variable_offset
address_low += variable_contribution
memory_factor = gamma + linearize(address_space, address_low, high, timestamp, value)
```

Changing coefficient must scale only the optional variable term.

## Failure

The generator branch loaded `variable_offset` into a temporary, multiplied the already accumulated `address_low` by `coefficient`, and then added the unscaled variable offset. It would emit:

```text
coefficient * (base_address_low + constant_offset) + variable_offset
```

instead of the intended affine expression. Coefficients zero or one and specially chosen values could hide the discrepancy.

## Adversarial or failure flow

1. Select a sparse delegation layout with a nontrivial variable-dependent coefficient.
2. Invoke the affected quotient-generator branch.
3. If artifact generation and compilation otherwise succeed, emit the wrong address expression into the quotient evaluator.
4. A prover targeting that hypothetical verifier could construct stage-2 products and quotient evaluations for the wrong memory tuple.
5. DEEP/FRI would then authenticate the generated relation rather than recover the intended affine expression.

In the historical revision, however, `IndirectAccessColumns::ToTokens` emitted a bare tuple where `Option<(...)>` required `Some((...))`. The same variable-dependent sparse layout therefore failed generated-source compilation, and the checked-in verifier artifacts did not contain this wrong expression. There was no historical accepting verifier for the card's former adversarial flow.

## Impact and fix

Had the branch reached a compiled verifier, its RAM tuple would have referred to the wrong location, breaking memory soundness or honest proofs. The fix multiplies `variable_offset` by the coefficient and adds that result to the existing `address_low`; the same commit separately repairs the serializer that blocked artifact compilation.

For every generated affine expression, preserve an AST-level oracle and compare emitted arithmetic term by term. Commutativity does not justify moving coefficients across additions.

## Regression

- Use coefficients `0`, `1`, `2`, and the maximum supported nontrivial value.
- Choose unequal base, constant, and variable values so both formulas differ.
- Compare circuit witness address, prover tuple, generator AST, emitted verifier result, and memory-product factor.
- Cover read and write sparse accesses plus carry/no-carry variants.
- Mutate only the variable offset and verify the coefficient scales the delta exactly.

## Reproduction evidence

```sh
git diff 6327a202048659bd8afac3b65cf65bb7e2ed9fc3 9b955b649cfbd1ef04305ec15af344dc5a41354f -- verifier_generator/src/inlining_generator/grand_product_accumulators.rs
```
