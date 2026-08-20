# Mersenne31 constructors reduced large values incorrectly

## Classification

- Confirmed historical field-arithmetic correctness bug
- Component: Mersenne31 signed/two's-complement reduction and canonical `u64` constructor
- Budget relevance: challenge support, canonical decoding, and algebraic equality assumptions depend on exact field mapping
- Reachability: concrete verifier severity depends on which proof/transcript/parser call sites accepted attacker-controlled large inputs
- Fixed by: [`03c4daf`](https://github.com/matter-labs/zksync-airbender/commit/03c4daff5c80a918ecd5fc58a1733f3108c6eae8)
- Vulnerable revision: `769ec2e3937fa591221e8f27dab66273c8ab1ffb`

## Field context

For Mersenne modulus `p = 2^31 - 1`, reduction can fold 31-bit chunks because `2^31 ≡ 1 (mod p)`. When a `u64` carries a signed/two's-complement intermediate, bits 62 and 63 need explicit treatment; ignoring one high chunk changes the represented residue.

The `PrimeField::from_u64` constructor has a different contract: it returns `Some` only when the full integer is already canonical `< p`. It must compare before narrowing.

## Intended mappings

```text
from_u64(x):
    Some(field(x)) iff full 64-bit x < p
    None otherwise

from_negative_u64_with_reduction(bits):
    field element equal to the exact intended signed/two's-complement integer modulo p
    using all 64 input bits
```

These contracts must match native, circuit, transcript, and EVM field representations.

## Failure

`from_negative_u64_with_reduction` split only bits `0..30` and `31..61`, used bit 63 as one sign correction, and failed to account correctly for the full top two-bit chunk. Its folding/sign adjustment produced wrong residues for large values.

Separately, `PrimeField::from_u64` compared `value as u32` with the modulus. Values above `2^32` could truncate to a small low word, pass the canonicality check, and be returned as though the original `u64` were canonical.

## Failure flow

1. Supply or derive a 64-bit value with meaningful high bits.
2. In the reducing path, drop/mishandle part of the top chunk and obtain the wrong residue.
3. In the canonical constructor, truncate before comparison and accept a noncanonical integer when its low word is `< p`.
4. Use the resulting element in transcript conversion, constant generation, verifier arithmetic, or proof parsing.
5. Diverge from another implementation or admit multiple integer encodings for one intended field-value contract.

The commit confirms arithmetic defects. A soundness report must still trace a reachable attacker-controlled call site before asserting challenge bias or proof malleability.

## Impact and fix

Large signed intermediates could map to the wrong field element, and large noncanonical unsigned values could be accepted after truncation. The fix performs complete Mersenne folding including bits 62–63 and compares the full `u64` against `ORDER` before casting.

Field bugs invalidate probability calculations if they alter challenge support or permit ambiguous proof encodings. Budget review must validate the actual hash-to-field/decoder path, not assume the abstract field API is correct.

## Regression

- Differential-test against big-integer/reference modular arithmetic over boundary and random 64-bit patterns.
- Include `0`, `p-1`, `p`, `2^31`, `2^32`, `2^62`, `2^63`, signed extremes, and `u64::MAX`.
- Assert `from_u64` rejects every value `>= p` without narrowing.
- Compare native, GPU, RISC-V/recursive, and Solidity/Yul conversions where applicable.
- Enumerate verifier-facing call sites and test noncanonical proof inputs separately from internal arithmetic.

## Reproduction evidence

```sh
git diff 769ec2e3937fa591221e8f27dab66273c8ab1ffb 03c4daff5c80a918ecd5fc58a1733f3108c6eae8 -- field/src/base.rs
```
