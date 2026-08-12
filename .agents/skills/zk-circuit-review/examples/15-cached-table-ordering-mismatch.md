# Fixed-table row order disagreed with cached multiplicity indices

## Classification

- Confirmed historical lookup-relation bug
- Components: Keccak Iota XOR, AND-NOT, and 16-bit rotate-left tables
- Bug class: physical table order inconsistent with custom index encoding
- Fixed by: [`b6142cd`](https://github.com/matter-labs/zksync-airbender/commit/b6142cd19dcad77dfc4993ce83c4825229610773)
- Vulnerable revision for reproduction: `b859a1114e6124108eccf62c3891c212d4cb4796`

## Intended relation

Cached multiplicity updates address a fixed-table row by a dense key encoding. For two bytes the index was `a | (b << 8)`, so `a` must vary fastest in physical row order. For rotations the index was `word | (rotation << 16)`, so the 16-bit word must vary fastest.

## Vulnerable relation

The key vectors used the opposite loop nesting: `b` varied fastest for the byte tables, and `rotation` varied fastest for the rotate table. Thus physical row `a | (b << 8)` held the key pair `(b, a)` rather than `(a, b)`; the rotation table had the analogous transposition. The byte-key orderings coincide only on the `a = b` diagonal, so symmetric or diagonal smoke inputs could conceal the mismatch.

## Security impact

Lookup queries and cached multiplicity counters referred to different table rows. For non-symmetric operations such as AND-NOT, Iota-controlled XOR, and rotation, this breaks the relation between inputs and outputs. Honest executions can fail, and any proof path that relies on the inconsistent cached index no longer establishes membership in the intended tuple table.

## Fix

The nested loops were reversed so their fastest-varying key component matches the low bits of the custom index function in all three tables.

## Audit lesson

Review table contents, dense index functions, physical row order, and multiplicity updates as one invariant. Test `row[index(key)] == key || output(key)`; checking that every key appears somewhere in the table is insufficient.

## Regression test

- For every row of the byte tables, assert that the row stored at `a | (b << 8)` has keys `(a,b)` and the native reference output.
- Sample boundary words and all rotation constants and assert the row at `word | (rotation << 16)` matches the reference split rotation.
- Run the same test through the cached multiplicity lookup path, not only the ordinary key lookup API.

## Reproduction evidence

```sh
git diff b859a1114e6124108eccf62c3891c212d4cb4796 b6142cd19dcad77dfc4993ce83c4825229610773 -- \
  cs/src/tables.rs
```
