# Keccak's disabled-row table key produced live state indices

## Classification

- Historical padding-witness and multiplicity-generation defect; no proved-state escape
- Evaluation status: non-scored witness-generation bug
- Components: Keccak-special delegation circuit and permutation-index fixed tables
- Bug class: disabled-row/padding key mapped to nonzero table outputs
- Fixed by: [`9ae55e6`](https://github.com/matter-labs/zksync-airbender/commit/9ae55e6839e53bde06ef52d642397491a75bb959)
- Vulnerable revision for reproduction: `f6c449e571aed0c2e030e4ccbec11c6c09785204`

## Intended relation

When all Keccak precompile and iteration flags are disabled, the packed control word is zero. That padding row must be a no-op: the permutation-index lookup must return zero indices so inactive rows cannot select live state elements or form nonzero indirect-access offsets.

## Vulnerable relation

For `control = 0`, both bitmask `trailing_zeros` results are `64`. The table had no explicit padding case and fell through to its junk default `[0,1,2,3,4,5]`. These outputs were assigned to state-index variables that feed the circuit's indirect memory-access construction.

## Effect

The shipped padding oracle supplied zero offsets, which disagreed with the old
table's `[0,1,2,3,4,5]` outputs; the lookup-only resolver also skipped required
multiplicity generation. This broke honest padded witness construction.

It did not create a state-isolation soundness gap. On inactive delegation rows,
ABI fields, timestamps, and indirect read/write values are forced to zero. A
satisfying assignment using the table's nonzero indices exists, and each read
and write uses the same derived address with identical zero data and timestamp,
so its memory factors cancel. The indices do not reach authenticated machine
state or a public claim.

## Fix

The permutation-index table now has an explicit zero-control case and returns six zero indices. The same fix adjusted lookup handling in the Keccak circuit so the padding convention is represented consistently.

## Audit lesson

Evaluate every lookup and memory-query constructor on its disabled selector, especially when zero is decoded with bit operations such as `trailing_zeros`. Trace all downstream relations before deciding whether a bad padding value changes the accepted relation or only the honest witness convention.

## Regression test

- Query each Keccak permutation-index table at control zero and assert all outputs are zero.
- Build a padded circuit row and assert every derived state index and indirect-access offset is the designated padding value.
- Verify a valid proof whose trace contains padding after the last active Keccak row.

## Reproduction evidence

```sh
git diff f6c449e571aed0c2e030e4ccbec11c6c09785204 9ae55e6839e53bde06ef52d642397491a75bb959 -- \
  cs/src/delegation/keccak_special5/mod.rs \
  cs/src/tables/keccak_precompile_related.rs
```
