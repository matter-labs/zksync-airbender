# Keccak Iota table omitted the circuit's fictitious final round

## Classification

- Confirmed historical semantic and completeness bug
- Component: Keccak-special Iota XOR fixed table
- Bug class: reachable control value missing from table contents
- Fixed by: [`7306247`](https://github.com/matter-labs/zksync-airbender/commit/73062473b8632d865b6f2c8c2ebe8303e5df242a)
- Vulnerable revision for reproduction: `d1098e4d2d70ff23be59f5c864e2649eee3dab9e`

## Intended relation

The Keccak-special schedule includes a circuit-specific, adjusted transition at control round `24`. Its Iota lookup must XOR each selected byte with the corresponding byte of adjusted constant `0x8000000080008008`. The permutation-index table already treated round 24 as reachable for the Iota/column-XOR phase.

## Vulnerable relation

The Iota table contained only 24 constants and applied them only for `round < 24`. At round 24 it selected the fallback value zero, turning the required XOR into the identity function even though the surrounding control table enabled that round.

## Security impact

The fixed table enforced a state transition different from the circuit's intended Keccak schedule. A trace following the required adjusted final transition could not satisfy the lookup, while a trace omitting that constant matched the faulty circuit relation.

## Fix

The table gained the adjusted 25th constant and changed its condition to `round <= 24`, aligning the table domain with the control schedule.

## Audit lesson

Cross-check the reachable control domain of every table against its constants array and fallback behavior. Special padding or normalization rounds are easy to omit when one component counts protocol rounds and another counts circuit transitions.

## Regression test

- Enumerate every reachable `(round, byte_position)` control and compare the table output with a reference constant array.
- Assert that the maximum enabled round in the control/index table equals the maximum handled round in the Iota table.
- Include a valid end-to-end Keccak-special trace that exercises round 24.

## Reproduction evidence

```sh
git diff d1098e4d2d70ff23be59f5c864e2649eee3dab9e 73062473b8632d865b6f2c8c2ebe8303e5df242a -- \
  cs/src/tables/keccak_precompile_related.rs
```
