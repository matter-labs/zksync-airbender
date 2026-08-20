# Sparse delegation quotient scaled the address itself

## Classification

- Confirmed historical generated-quotient relation bug
- Component: delegation RAM tuple evaluation for variable-dependent sparse access
- Reduction location: address derivation → memory compression → grand-product quotient
- Security character: generated verifier accepted a different address formula from the circuit specification
- Fixed by: [`9b955b6`](https://github.com/matter-labs/zksync-airbender/commit/9b955b649cfbd1ef04305ec15af344dc5a41354f)
- Vulnerable revision: `6327a202048659bd8afac3b65cf65bb7e2ed9fc3`

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

Generated code loaded `variable_offset` into a temporary, multiplied the already accumulated `address_low` by `coefficient`, and then added the unscaled variable offset. It enforced:

```text
coefficient * (base_address_low + constant_offset) + variable_offset
```

instead of the intended affine expression. Coefficients zero or one and specially chosen values could hide the discrepancy.

## Adversarial or failure flow

1. Select a sparse delegation layout with a nontrivial variable-dependent coefficient.
2. Construct memory tuples under the verifier's wrong address formula.
3. Build stage-2 products and quotient evaluations matching that generated relation.
4. Prove the quotient's low degree through DEEP/FRI.
5. Obtain acceptance for a memory access relation different from the compiled circuit—unless another committed address/carry constraint independently pins the intended expression.

An honest prover following the circuit formula instead fails verification. Because the bug is in verifier generation, reviewers must analyze both outcomes rather than classify it as parity only.

## Impact and fix

The generated verifier's RAM tuple could refer to the wrong location for sparse delegation accesses, breaking memory soundness or honest proofs. The fix multiplies `variable_offset` by the coefficient and adds that result to the existing `address_low`.

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
