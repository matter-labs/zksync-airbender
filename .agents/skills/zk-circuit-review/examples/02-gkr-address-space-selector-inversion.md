# Cached GKR memory tuples inverted the register/RAM address-space tag

## Classification

- Confirmed historical compiler relation bug; soundness-critical and also capable of breaking completeness
- Component: GKR compiler, cached memory-permutation expressions
- Bug class: Boolean polarity disagreed with enum encoding
- Fixed by: [`b5021bc`](https://github.com/matter-labs/zksync-airbender/commit/b5021bcd4c68d4c691a7df1ce11ce49b9222e272)
- Vulnerable revision for reproduction: `725892f1727a7eaa411c8b2303cc8cecfa19410d`

## Intended relation

The memory tuple includes an address-space tag. Its encoding was:

```text
Register = 0
RAM      = 1
PC       = 2
```

`AddressSpaceIsRegister::Is(v)` means `v = 1` on a register access and `v = 0` on a RAM access. The numeric tuple tag therefore has to be `1 - v`, not `v`.

Conversely, `AddressSpaceIsRegister::Not(v)` represents the logical negation, so its numeric tag has to be `v`.

## Vulnerable relation

`mem_permutation_expr_into_cached_expr` compiled the two variants without converting between Boolean meaning and numeric tag:

```text
Is(v)  -> v
Not(v) -> 1 - v
```

The resulting truth table was exactly reversed:

| Actual access | `v` | Required tag | Vulnerable tag |
|---|---:|---:|---:|
| register | 1 | 0 | 1 |
| RAM | 0 | 1 | 0 |

This affected the cached GKR grand-product relation, so the erroneous values were part of the proved tuple rather than a witness-generation-only mistake.

## Security impact

The permutation argument authenticates tuple equality, not the semantic meaning of a mislabeled tag. Swapping tags breaks register/RAM domain separation and can make a local access authenticate against the wrong global memory domain. Depending on the surrounding initialization and teardown tuples, the result is an invalid accepted state relation, an honest-proof failure, or both.

## Fix

The compiler asserted `Register as u8 == 0` and inverted the compiled forms:

```text
Is(v)  -> Not(v)  = 1 - v
Not(v) -> Is(v)   = v
```

## Audit lesson

For every tagged permutation or lookup tuple, write the producer's complete truth table and compare it with the protocol's numeric encoding. Names such as `is_register` do not imply that the encoded field is `1` for registers. Check cached and uncached lowering paths separately.

## Regression test

- Add a table-driven compiler test for all four cases: `Is(false)`, `Is(true)`, `Not(false)`, and `Not(true)`. Assert the resulting numeric tags against `Register = 0` and `RAM = 1`.
- Compile the same valid memory trace with caches enabled and disabled and assert identical evaluated memory tuples and grand-product contributions.
- Include at least one register and one RAM access at the same numeric address to ensure the test observes the address-space field rather than only address/value fields.

## Reproduction evidence

```sh
git diff 725892f1727a7eaa411c8b2303cc8cecfa19410d b5021bcd4c68d4c691a7df1ce11ce49b9222e272 -- \
  cs/src/gkr_compiler/utils.rs
```
