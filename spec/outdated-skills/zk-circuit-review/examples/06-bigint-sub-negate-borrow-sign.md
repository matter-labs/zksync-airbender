# Bigint SUB_NEGATE used the wrong sign for the input borrow

## Classification

- Confirmed historical soundness bug
- Component: 256-bit delegated arithmetic circuit
- Bug class: incorrect carry/borrow sign in the first limb of a shared recurrence
- Fixed in merged history by: [`e88874c`](https://github.com/matter-labs/zksync-airbender/commit/e88874cea50cd7287521fa5a25023df866343ae4), PR [#135](https://github.com/matter-labs/zksync-airbender/pull/135)
- Original equivalent fix commit: [`10ce008`](https://github.com/matter-labs/zksync-airbender/commit/10ce00819e0da9274548bbf53c2e53d092827f5f)
- Later branch-equivalent fix: [`6b32454`](https://github.com/matter-labs/zksync-airbender/commit/6b3245469cf441af124309adaee56e6cc24cd0c6)
- Vulnerable revision for reproduction: `9be0cc36dc3f9559ddb33af552dfa8e42102ab66`

## Intended relation

`SUB_NEGATE` computes `b - a - input_borrow` across sixteen 16-bit limbs. For limb zero, the selected shared addition-form constraint is:

```text
a_i + result_i - b_i + input_borrow - 2^16 * output_borrow = 0
```

Rearranged, this is:

```text
result_i = b_i - a_i - input_borrow + 2^16 * output_borrow
```

Later limbs add the previous output borrow with the same sign.

## Vulnerable relation

Only the first-limb `SUB_NEGATE` branch subtracted `input_borrow` in the constraint. This changed its semantics to:

```text
result_i = b_i - a_i + input_borrow + 2^16 * output_borrow
```

An asserted borrow therefore added one instead of subtracting one. The honest witness generator and the enforced recurrence disagreed; soundness is determined by the latter.

## Security impact

Whenever `SUB_NEGATE` began with an asserted borrow, the constrained operation differed from the specified subtraction by two in the least-significant limb before propagation. This was a branch-specific soundness error: zero-borrow tests and the ordinary SUB branch could both pass while the delegated operation proved the wrong 256-bit result.

## Fix

The `perform_sub_negate * carry_or_borrow` term changed from subtraction to addition, matching the witness algorithm and the algebra above.

## Audit lesson

Derive every multi-limb recurrence on paper, including the first-limb carry-in convention. Do not infer correctness from shared code: a single branch-specific sign can invalidate only one operation and only when carry-in is set, making ordinary zero-carry tests miss it.

## Regression test

- Compare `SUB_NEGATE` against a 256-bit reference for both input-borrow values, including cases that do and do not propagate across several zero limbs.
- Include the simple valid case `b = 5`, `a = 0`, input borrow `1`, expected result `4`.
- Assert every intermediate borrow bit as well as the final limbs, then prove and verify the delegated call.

## Reproduction evidence

```sh
git diff 9be0cc36dc3f9559ddb33af552dfa8e42102ab66 e88874cea50cd7287521fa5a25023df866343ae4 -- \
  cs/src/delegation/bigint_with_control/mod.rs

# The same one-line correction was later applied on another historical branch:
git diff 8430199125c0f9d78394e2b96e8ba795bc7c6173 6b3245469cf441af124309adaee56e6cc24cd0c6 -- \
  cs/src/delegation/bigint_with_control/mod.rs
```
