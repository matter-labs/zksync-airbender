# Mersenne31 constructors reduced large values incorrectly

## Classification

- Confirmed historical field-arithmetic correctness bug
- Fixed by: [`03c4daf`](https://github.com/matter-labs/zksync-airbender/commit/03c4daff5c80a918ecd5fc58a1733f3108c6eae8)
- Vulnerable revision: `769ec2e3937fa591221e8f27dab66273c8ab1ffb`

## Failure

`from_negative_u64_with_reduction` ignored the top two bits except for one sign adjustment and used an incorrect folding formula. `PrimeField::from_u64` compared `value as u32` with the modulus, so values above `2^32` could truncate into an apparently canonical field element.

## Impact and fix

Transcript challenges, constants, or verifier arithmetic constructed through these paths could represent the wrong field element or accept a noncanonical integer. The fix performs complete Mersenne folding and compares the full u64 before narrowing.

## Regression

Differential-test both constructors against big-integer modulo arithmetic at 0, `p-1`, `p`, `2^32`, `2^62`, `2^63`, and `u64::MAX`.

```sh
git diff 769ec2e3937fa591221e8f27dab66273c8ab1ffb 03c4daff5c80a918ecd5fc58a1733f3108c6eae8 -- field/src/base.rs
```
