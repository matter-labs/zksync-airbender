# SRA fixed table set low fill bits instead of high fill bits

## Classification

- Confirmed historical soundness bug with completeness consequences
- Component: fixed table for arithmetic-right-shift sign filling
- Bug class: table generation encoded the intended mask in the wrong bit direction
- Fixed by: [`fa26bd6`](https://github.com/matter-labs/zksync-airbender/commit/fa26bd621fa6b02e8eb18164a5dc2163817151de)
- Vulnerable revision for reproduction: `79ff94f89470b8ab6dd2518f5c14e21cdf8d15e1`

## Intended relation

For a negative 32-bit word shifted right by `s`, the sign-fill mask must set the highest `s` bits:

```text
mask = 0xffffffff << (32 - s)
```

The table splits this mask into low and high 16-bit outputs. The circuit adds them to logical-right-shift contributions.

## Vulnerable relation

The table used:

```text
0xffffffff >> (32 - s)
```

This sets the lowest `s` bits. Because the table itself is the constraint's source of truth, the proof system faithfully enforced the wrong arithmetic relation.

## Security impact

For every negative input and nonzero shift, the fixed table defined a low-bit fill instead of sign extension at the top of the word. Since that table was the enforced relation's source of truth, the circuit proved an operation different from RV32 SRA and rejected the correct result.

## Fix

The table changed from a right shift to an unbounded left shift, producing the highest-bit mask and preserving the shift-zero case.

## Audit lesson

Fixed tables are executable specifications, not trusted constants. Independently recompute representative boundary rows: shift 0, shift 1, maximum shift, positive sign, and negative sign. Compare full words before and after limb splitting.

## Regression test

- Exhaustively compare all table rows' fill masks with `(((value as i32) >> shift) as u32) ^ (value >> shift)` for representative high limbs and every shift `0..31`.
- Include the boundary vector `0x80000000 >> 5 = 0xfc000000`, plus shifts 0, 1, 15, 16, and 31.
- Assert both the recombined 32-bit mask and its two 16-bit table outputs.

## Reproduction evidence

```sh
git diff 79ff94f89470b8ab6dd2518f5c14e21cdf8d15e1 fa26bd621fa6b02e8eb18164a5dc2163817151de -- \
  cs/src/tables/shift_opcode_related.rs
```
