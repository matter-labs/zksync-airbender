# Keccak's disabled-row table key produced live state indices

## Classification

- Confirmed historical completeness and state-isolation bug
- Components: Keccak-special delegation circuit and permutation-index fixed tables
- Bug class: disabled-row/padding key mapped to nonzero table outputs
- Fixed by: [`9ae55e6`](https://github.com/matter-labs/zksync-airbender/commit/9ae55e6839e53bde06ef52d642397491a75bb959)
- Vulnerable revision for reproduction: `f6c449e571aed0c2e030e4ccbec11c6c09785204`

## Intended relation

When all Keccak precompile and iteration flags are disabled, the packed control word is zero. That padding row must be a no-op: the permutation-index lookup must return zero indices so inactive rows cannot select live state elements or form nonzero indirect-access offsets.

## Vulnerable relation

For `control = 0`, both bitmask `trailing_zeros` results are `64`. The table had no explicit padding case and fell through to its junk default `[0,1,2,3,4,5]`. These outputs were assigned to state-index variables that feed the circuit's indirect memory-access construction.

## Security impact

Disabled rows were not isolated from live state. Padding could create nonzero state selections and memory tuples, contaminating the RAM argument or making an otherwise valid padded trace unsatisfiable. Any masking assumption downstream had to compensate for a table that already violated the zero-row convention.

## Fix

The permutation-index table now has an explicit zero-control case and returns six zero indices. The same fix adjusted lookup handling in the Keccak circuit so the padding convention is represented consistently.

## Audit lesson

Evaluate every lookup and memory-query constructor on its disabled selector, especially when zero is decoded with bit operations such as `trailing_zeros`. A zero flag does not make computed lookup outputs disappear unless every downstream relation is explicitly gated.

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
