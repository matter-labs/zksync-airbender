# MULMOD and FMAMOD omitted the Montgomery representation correction

## Classification

- Confirmed historical soundness bug
- Component: GKR add/sub/LUI/AUIPC/modular-operations family
- Bug class: constraint arithmetic used the wrong field representation
- Fixed by: [`a16b6ec`](https://github.com/matter-labs/zksync-airbender/commit/a16b6ec1196f700798f7c3d802a9c07c8500e9ea), PR [#309](https://github.com/matter-labs/zksync-airbender/pull/309)
- Vulnerable revision for reproduction: `6e9cd7d594bf606b9dad26c8456a4f5e311d275a`

## Intended relation

MULMOD and FMAMOD operate on 32-bit machine words interpreted as raw representatives of the circuit field. When the field backend uses Montgomery representation, multiplying two such word expressions requires the representation correction described by the fix as an `R^-1` factor.

Symbolically, the multiplication term must be:

```text
a * b * R^-1
```

for Montgomery-backed `F`, while a non-Montgomery field uses `a * b`.

## Vulnerable relation

The circuit always constrained the intermediate as:

```text
z = a * b + is_fmamod * old_rd
```

It omitted the conditional Montgomery factor. Witness generation and machine semantics used the raw-representation conversion, so the polynomial relation authenticated a differently scaled product.

## Security impact

On a Montgomery-backed field, the constrained product was scaled differently from the machine word operation. MULMOD and FMAMOD could therefore prove output words that were not the specified modular products. The bug was not exposed by previous tests because their binaries did not execute these modular-operation instructions; PR #309 added such coverage.

## Fix

The fix introduced `montgomery_product_expr(a, b)`. It multiplies by `F::from_reduced_raw_repr(1)` when `F::IS_MONT_REPR` and otherwise leaves the product unchanged. Witness conversion was updated to use the corresponding raw-representation operations.

## Audit lesson

Track the representation of every value crossing word arithmetic and field arithmetic. A field element's mathematical value, canonical integer, raw limb encoding, and Montgomery storage are not interchangeable. Compare the constraint expression, witness conversion, and output encoding under every supported field backend.

## Regression test

- Run MULMOD and FMAMOD over a matrix containing zero, one, `p-1`, and several nontrivial word values; compare with a canonical integer modular-arithmetic reference.
- Execute the same semantic tests with a Montgomery-backed field and a non-Montgomery test field when supported.
- Assert the generated expression contains the representation-correction constant exactly when `F::IS_MONT_REPR` is true, then prove and verify the instruction binary added by PR #309.

## Reproduction evidence

```sh
git diff 6e9cd7d594bf606b9dad26c8456a4f5e311d275a a16b6ec1196f700798f7c3d802a9c07c8500e9ea -- \
  cs/src/gkr_circuits/add_sub_family/circuit.rs \
  cs/src/gkr_circuits/utils.rs
```
