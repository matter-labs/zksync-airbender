# Modular canonicality recurrence added the output high limb instead of subtracting it

## Classification

- Confirmed historical soundness bug
- Component: GKR add/sub/LUI/AUIPC/modular-operations family
- Bug class: wrong sign in a multi-limb reduction constraint
- Fixed by: [`a16b6ec`](https://github.com/matter-labs/zksync-airbender/commit/a16b6ec1196f700798f7c3d802a9c07c8500e9ea), PR [#309](https://github.com/matter-labs/zksync-airbender/pull/309)
- Vulnerable revision for reproduction: `6e9cd7d594bf606b9dad26c8456a4f5e311d275a`

## Intended relation

To prove that a modular result is canonical, the circuit range-checks a two-limb temporary and proves the wrapping subtraction:

```text
tmp = out - p mod 2^32
borrow = 1
```

Equivalently:

```text
tmp + p = out + 2^32
```

For base `B = 2^16`, its high-limb recurrence is:

```text
carry_low + tmp_high + p_high - out_high - B*borrow = 0
```

## Vulnerable relation

The high-limb equation used `+ out_high` instead of `- out_high`. The low-limb equation and forced final borrow were otherwise present. This no longer represented subtraction by the modulus and could admit a noncanonical field-equivalent output with a fabricated range-valid temporary.

## Security impact

The two limb equations no longer recombined to `tmp + p = out + 2^32`. Consequently the canonicality gadget did not establish `out < p`; a range-valid temporary could satisfy an unrelated high-limb identity while the field equation supplied only congruence modulo `p`. The affected modular instructions could therefore prove noncanonical machine outputs.

## Fix

The high-limb expression changed from `+ out_high` to `- out_high`, restoring the combined 32-bit subtraction relation.

## Audit lesson

Recombine limb equations into the claimed full-width identity and check the solution space, not only the honest witness path. Range-checked carry and temporary limbs do not rescue an equation with the wrong sign. Test boundary representatives around `0` and `p` when reviewing canonicity gadgets.

## Regression test

- Symbolically recombine the emitted low- and high-limb expressions in a unit test and assert that their coefficients match `tmp + p - out - 2^32*borrow`.
- Exercise ADDMOD, SUBMOD, MULMOD, and FMAMOD on results near zero and near `p-1`; assert the output is canonical and the subtraction temporary/carries match a 32-bit reference.
- Include `0 + 0 mod p = 0` as a boundary case and prove/verify the resulting valid trace.

## Reproduction evidence

```sh
git diff 6e9cd7d594bf606b9dad26c8456a4f5e311d275a a16b6ec1196f700798f7c3d802a9c07c8500e9ea -- \
  cs/src/gkr_circuits/add_sub_family/circuit.rs
```
