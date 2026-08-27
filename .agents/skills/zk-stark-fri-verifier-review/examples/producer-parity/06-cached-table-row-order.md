# Cached lookup tables used the wrong row order

## Classification

- Producer-parity history: confirmed historical cached-multiplicity indexing bug
- Component: fixed Keccak XOR/Iota, ANDN, and ROTL lookup tables
- Reduction location: tuple → cached multiplicity index → setup-table row
- Security character: lookup witness/setup mismatch; generally honest-proof failure unless every accepting path shares the same unintended tuple permutation
- Fixed by: [`b6142cd`](https://github.com/matter-labs/zksync-airbender/commit/b6142cd19dcad77dfc4993ce83c4825229610773)
- Vulnerable revision: `b859a1114e6124108eccf62c3891c212d4cb4796`

## Protocol context

Cached lookup counting maps a tuple directly to a row index instead of searching the fixed table. That optimization is correct only if the table polynomial enumerates tuples in exactly the same axis order as the index formula.

For two-dimensional tables, swapping loop nesting permutes rows while preserving the table as an unordered set. LogUp/multiplicity arguments are row-aligned: multiplicity at row `i` weights setup tuple at row `i`, so set equality alone is insufficient.

## Intended row relation

```text
row = cached_index(tuple)
setup_table[row] == tuple
multiplicity[row] == number of execution lookups for tuple
```

For XOR/Iota and ANDN, the canonical fast-changing axis must match cached `(a,b)` packing. For ROTL, word/rotation nesting must match its index packing.

## Failure

XOR/Iota and ANDN tables iterated `a` outside `b`, while cached multiplicity access expected the opposite nesting. ROTL iterated the 16-bit word outside the rotation constant, again opposite the cached row formula.

Consequently, multiplicity slot `i` counted one tuple while setup-table row `i` contained another. Table membership tests could still pass because all tuples were present, masking the positional error.

## Failure flow

1. Execute a lookup for tuple `t` and compute cached index `i`.
2. Increment multiplicity `m[i]`.
3. Commit a setup table whose row `i` contains permuted tuple `t'`.
4. Form the lookup table side using `m[i]` against `t'`.
5. Fail the global lookup identity unless the execution multiset is accidentally symmetric under the row permutation.

This is primarily completeness/correctness. A soundness issue would require the verifier/circuit to interpret the permuted table as the intended operation while allowing a false semantic tuple; that must be shown from the complete constraints.

## Impact and fix

Cached multiplicities were paired with the wrong fixed-table values. The fix swaps loop nesting: `b` outer/`a` inner for XOR/Iota and ANDN, and rotation outer/word inner for ROTL, matching cached index order. Generated layouts/binaries changed accordingly.

Treat table order as part of the committed setup. Any cache formula must have an executable inverse checked against the actual setup rows.

## Regression

- Round-trip representative and boundary tuples through `tuple -> cached index -> setup row`.
- Exhaustively test smaller analogues and sample full production tables.
- Compare CPU, GPU, cached counter, generated setup, and verifier opening order.
- Use nonsymmetric multiplicity distributions so row permutations cannot cancel.
- Fingerprint regenerated verifier/setup artifacts after table-order changes.

## Reproduction evidence

```sh
git diff b859a1114e6124108eccf62c3891c212d4cb4796 b6142cd19dcad77dfc4993ce83c4825229610773 -- cs/src/tables.rs
```
