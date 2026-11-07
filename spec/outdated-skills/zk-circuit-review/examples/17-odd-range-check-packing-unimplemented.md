# An odd range-check count entered an unimplemented compiler path

## Classification

- Confirmed historical broken-completeness bug
- Components: one-row circuit compiler and paired 16-bit lookup layout
- Bug class: odd-sized obligation list routed into unsupported remainder handling
- Fixed by: [`f6c449e`](https://github.com/matter-labs/zksync-airbender/commit/f6c449e571aed0c2e030e4ccbec11c6c09785204)
- Vulnerable revision for reproduction: `14921e8c67132635442e5eaf3c2625c9110a2009`

## Intended relation

The prover batches two 16-bit range-check expressions into each lookup accumulator. Every requested expression must be covered even when the circuit produces an odd count. Repeating one expression is semantically harmless because membership in the same range table is idempotent.

## Vulnerable relation

The compiler allowed an odd `range_check_16_lookup_expressions` list and represented its last item through `remainder_for_range_check_16`. The Keccak delegation layout reached this state. Downstream layout, cached-data, quotient, and boundary code required even pairs or contained `todo!()` branches whenever the remainder was present.

The concrete historical failure was fail-closed: circuit proving or verifier generation could panic on the unsupported remainder. The available code does not support the stronger claim that the final range check was silently discarded.

## Security impact

A valid circuit whose collected range-check obligations had odd cardinality could compile into an artifact that the proving pipeline could not process. In the affected Keccak layout, `remainder_for_range_check_16` was non-null while the relevant prover paths were explicitly unimplemented, preventing complete proof generation rather than weakening the range relation.

## Fix

The compiler now asserts that directly placed 16-bit range-check columns are pairable. If the complete expression list is odd, it duplicates the last expression before constructing the witness and stage-two layouts. The Keccak artifact consequently changes from an unsupported remainder to one ordinary pair containing the same lookup twice.

## Audit lesson

For every compiler pass that batches obligations in fixed-size groups, trace the remainder case through layout, witness generation, quotient construction, serialization, and verifier generation. A remainder field in an artifact is not evidence that the pipeline implements it; search every consumer for assertions, truncating iteration, and placeholder branches.

## Regression test

- Compile a minimal circuit containing one nontrivial 16-bit range-check expression and assert that the artifact contains two identical expressions, one ordinary pair, and no remainder.
- Compile circuits with zero, even, and odd counts and assert every original obligation occurs at least once in the paired list.
- Run proof generation and verification for the odd-count fixture so a layout-only test cannot miss a downstream unsupported branch.

## Reproduction evidence

```sh
git diff 14921e8c67132635442e5eaf3c2625c9110a2009 f6c449e571aed0c2e030e4ccbec11c6c09785204 -- \
  cs/src/one_row_compiler/compile_layout.rs \
  cs/keccak_delegation_layout.json
```
