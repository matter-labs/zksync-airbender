# Boundary check read the wrong grand-product column

## Classification

- Confirmed historical generated STARK verifier bug
- Fixed by: [`16b5aef`](https://github.com/matter-labs/zksync-airbender/commit/16b5aefcd6210859c5c281b8189ab366fe2b8411)
- Vulnerable revision: `1826de4ad588f6d14198bac8ee170993f503df81`

## Failure

The generated quotient evaluator enforced initial/final memory grand-product boundary values against stage-2 column 50. After the layout changed, the actual grand-product accumulator was column 51.

## Impact and fix

The verifier divided and batched a boundary numerator for the wrong polynomial, leaving the intended accumulator boundary unchecked while constraining an unrelated column. The fix derives the absolute grand-product column through the layout accessor and regenerates code.

## Regression

Structurally assert that every boundary constraint resolves its symbolic column through layout metadata, then mutate the true final accumulator independently.

```sh
git diff 1826de4ad588f6d14198bac8ee170993f503df81 16b5aefcd6210859c5c281b8189ab366fe2b8411 -- verifier_generator/src/inlining_generator/first_or_last_rows.rs verifier_generator/src/generated_inlined_verifier.rs
```
