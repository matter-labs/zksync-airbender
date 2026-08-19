# L1 inits/teardowns product ratio was reversed

## Classification

- Confirmed historical recursive accumulator-orientation bug
- Fixed by: [`f15c643`](https://github.com/matter-labs/zksync-airbender/commit/f15c64359f852837c9ffe4fe368a62f34b6e3c89)
- Vulnerable revision: `b75be7bbecc17860dac85a6d875887a7e7fb1396`

## Failure

The output array was ordered `[teardown/read, init/write]`, but code destructured it as `[init, teardown]` and accumulated `teardown / init`. Global memory closure expected the write/read orientation `init / teardown`.

## Impact and fix

Even individually valid recursion outputs combined into the inverse global product. The fix names the actual order and multiplies init then inverse teardown, with a machine-state closure self-check.

## Regression

Use distinct nonunit products for both sides and compare the recursive accumulator to a direct write/read calculation.

```sh
git diff b75be7bbecc17860dac85a6d875887a7e7fb1396 f15c64359f852837c9ffe4fe368a62f34b6e3c89 -- prover/src/gkr/prover/mod.rs
```
