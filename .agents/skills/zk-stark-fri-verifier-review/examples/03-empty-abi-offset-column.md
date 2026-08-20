# Empty ABI high limbs were read as real columns

## Classification

- Confirmed historical generated-verifier layout bug
- Component: delegation RAM/request quotient generation with optional ABI offset limbs
- Reduction location: zero-width layout range → quotient input expression
- Security character: wrong AIR or unusable generated code for layouts where the absent high limb semantically equals zero
- Fixed by: [`613c8de`](https://github.com/matter-labs/zksync-airbender/commit/613c8de2c215d498a0646c2c883f029f49fae6e8)
- Vulnerable revision: `23f5b8bf72b6ab68f4589a5db45561cda7974727`

## Protocol context

Some delegation layouts omit `abi_mem_offset_high` entirely because their ABI address fits the low-limb contract. The layout expresses absence as a zero-length column range. Algebraically, the missing high limb is the constant field zero; it is not an opening slot.

The generated quotient uses this value in delegation RAM conventions and request creation/processing. Calling `.start()` on an empty range still returns an integer, often the boundary shared with the next real column.

## Intended layout relation

```text
if abi_mem_offset_high.num_elements() == 1:
    high = opening[column_address(range.start)]
else if num_elements() == 0:
    high = 0
else:
    reject unsupported layout
```

The generator, opening inventory, and verifier cursor must agree that zero-width consumes no polynomial.

## Failure

The generator unconditionally called `abi_mem_offset_high.start()` and emitted a memory-subtree read. For an empty range, that offset identified a neighboring or out-of-contract column rather than an ABI high limb.

The verifier then inserted unrelated witness data into address/lookup expressions or generated an artifact whose opening references were inconsistent with the layout.

## Failure flow

1. Generate a valid circuit layout with zero ABI-high columns.
2. Resolve the empty range's start offset as though it named a column.
3. Read the adjacent memory-subtree opening.
4. Use that value as the address high limb in quotient relations.
5. Reject honest proofs using semantic zero, or accept a quotient for a relation polluted by an unrelated column if all other constraints permit it.

The severity depends on the neighboring column and complete AIR. The confirmed defect is that the generated verifier did not implement the declared optional-field semantics.

## Impact and fix

Valid zero-high-limb delegation layouts could not rely on a faithful quotient verifier. The fix branches on `num_elements()` at all three affected generator sites and emits `Mersenne31Field::ZERO` for the empty case.

Zero-width ranges are protocol variants. Audit every `.start()`, indexing operation, transcript slot, and opening count applied to optional layout ranges.

## Regression

- Generate otherwise identical layouts with zero and one ABI-high column.
- Assert zero-width emits a literal field zero and consumes no opening.
- Place a distinct sentinel in the adjacent column and prove it cannot influence ABI address evaluation.
- Compile and run the generated artifacts for request creation, request processing, and RAM conventions.
- Enumerate all optional ranges in the layout and require explicit zero-width handling.

## Reproduction evidence

```sh
git diff 23f5b8bf72b6ab68f4589a5db45561cda7974727 613c8de2c215d498a0646c2c883f029f49fae6e8 -- verifier_generator/src/inlining_generator/everywhere_except_last.rs
```
