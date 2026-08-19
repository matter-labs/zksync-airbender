# Cached lookup tables used the wrong row order

## Classification

- Confirmed historical cached-multiplicity indexing bug
- Fixed by: [`b6142cd`](https://github.com/matter-labs/zksync-airbender/commit/b6142cd19dcad77dfc4993ce83c4825229610773)
- Vulnerable revision: `b859a1114e6124108eccf62c3891c212d4cb4796`

## Failure

Several fixed tables enumerated the two key axes in the opposite nesting order from cached multiplicity access: XOR/Iota and ANDN iterated `a` outside `b`, while ROTL iterated words outside rotation constants.

## Impact and fix

Multiplicity index `i` referred to a different table tuple than the setup polynomial at row `i`, so lookup grand products were constructed from mismatched keys. The fix swaps loop nesting to the canonical cached-index order.

## Regression

For every table, round-trip representative tuples through `tuple -> row index -> setup row` and compare CPU/GPU/cache enumeration.

```sh
git diff b859a1114e6124108eccf62c3891c212d4cb4796 b6142cd19dcad77dfc4993ce83c4825229610773 -- cs/src/tables.rs
```
