# MEMCOPY was omitted from the merged range-check selector

## Classification

- Confirmed historical soundness bug
- Component: 256-bit delegated arithmetic circuit (`bigint_with_control`)
- Bug class: one operation omitted from a shared, selector-weighted range-check aggregate
- Fixed by: [`248413f7`](https://github.com/matter-labs/zksync-airbender/commit/248413f7), external audit patch (#1)
- Vulnerable revision for reproduction: `3f67e322`

## Intended relation

`additive_ops_result` holds the sixteen 16-bit result limbs of every additive
operation, and is deliberately allocated without its own range check:

```text
// NOTE: no range checks here, we will merge it with multiplication low
```

One shared block is then expected to range-check the selected result for *every*
operation that writes it, by summing selector-weighted terms and checking the
collapsed value once:

```text
t = perform_add*a + perform_sub*a + perform_sub_negate*a + perform_eq*a
    + perform_memcopy*a
    + perform_mul_low*b + perform_mul_high*b,   t < 2^16
```

MEMCOPY writes `additive_ops_result` through the same additive path, so it must
appear as a selector term.

## Vulnerable relation

The aggregate omitted `perform_memcopy`. On a MEMCOPY row every remaining
selector is zero, so the relation degenerates to `t = 0` and constrains nothing
about the written limbs. The deferred range check was never paid for that one
operation.

The limb recurrence cannot recover the bound on its own. Its carries are only
Boolean, not range-implied:

```text
limb 0:  b_0 + carry_in - r_0 - 2^16*of_0 = 0
limb i:  b_i + of_{i-1} - r_i - 2^16*of_i = 0
```

Setting `of_0 = 1` and `r_0 = p - 2^16` satisfies limb zero over the field while
every other relation stays satisfied, so an honest `b = 0` copy can be proved as
a write of a non-canonical limb.

## Security impact

MEMCOPY's destination limbs reach the indirect memory write with no canonical
16-bit bound, so the delegation can write values that are not valid machine
words while satisfying every constraint. Consumers treat memory-word limbs as
16-bit by provenance, so a forged limb propagates into later arithmetic and
memory histories.

The converse isolates the defect exactly: had `r_i` been range-checked, `of_0 = 1`
would have forced `b_0 = 2^16 - 1` and `carry_in = 1`, the genuine carry
condition. The missing selector term is the entire gap.

## Fix

`perform_memcopy` was added as a selector term in the merged range-check block, a
one-line change restoring the invariant that every operation writing the shared
result pays into the shared check.

## Audit lesson

A deferred or merged check is a debt that must be repaid on every branch that
uses the shared variable. When a comment says a check is merged elsewhere, find
that block and enumerate its selector terms against the complete list of
operations that write the variable — a missing term silently degrades the
relation to `0 = 0` on exactly the branch it was supposed to cover. Boolean
carries do not imply limb bounds, so a recurrence never substitutes for the
range check it was assumed to justify.

## Regression test

- Assert that the merged range-check aggregate's selector set equals the set of
  operations that write the shared result variable.
- For each operation, assert the constraint system rejects a witness whose result
  limb is outside `[0, 2^16)` while all other relations are satisfied.
- Prove and verify a MEMCOPY of a value whose low limb is `2^16 - 1` with carry
  set and clear, so the genuine carry path is exercised alongside the check.

## Reproduction evidence

```sh
git diff 3f67e322 248413f7 -- \
  cs/src/delegation/bigint_with_control/mod.rs
```
