# A full-width PoW threshold shift disabled grinding in optimized builds

## Classification

- Confirmed historical boundary bug, latent in shipped configurations
- Component: native Blake2s transcript prover/verifier, not an algebraic circuit
- Bug class: prover/verifier disagreement at an allowed exceptional value
- Fixed by: [`bbf919d`](https://github.com/matter-labs/zksync-airbender/commit/bbf919d517e693827c81d0f579c74e754399292f), PR [#322](https://github.com/matter-labs/zksync-airbender/pull/322)
- Vulnerable revision for reproduction: `a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0`

## Intended relation

For `pow_bits` in the accepted API range `0..=32`, prover search and verifier acceptance must use one threshold:

```text
threshold(bits) = floor((2^32 - 1) / 2^bits)
accept iff top_hash_word <= threshold(bits)
```

At `pow_bits = 32`, the threshold is zero, so only an all-zero top word passes.

## Vulnerable relation

The prover already used `u32::MAX.checked_shr(pow_bits).unwrap_or(0)`. The verifier independently used `0xffffffff >> pow_bits` while explicitly allowing `pow_bits == 32`. At that boundary, Rust debug builds panic on shift overflow. In optimized builds on the target path, the shift amount is masked to zero and the threshold becomes `0xffffffff`, so every top word passes.

## Security impact

If a future configuration selected 32 PoW bits, the prover would search using the intended zero threshold while an optimized verifier would enforce no grinding. Debug verification would abort instead. The repository's shipped security configurations were not affected: their largest configured phase was 28 bits, so this was a real but latent verifier foot-gun rather than an active deployed break.

## Fix

The transcript now exposes one `pow_threshold` helper using the checked shift. Both serial/parallel prover search and verifier checking call it. A boundary test fixes the expected results for `0`, `1`, `28`, `31`, and `32` bits.

## Audit lesson

Check exceptional values at the exact width of every shift, range, or decomposition, in both debug and optimized semantics. When prover and verifier compute the same protocol quantity, require one shared implementation or compare both across the entire declared input domain.

## Regression test

- Assert the threshold values at `0`, `1`, `31`, and `32` in both debug and release test profiles.
- Property-test equality between the prover-search threshold and verifier threshold for every allowed `pow_bits` value.
- Statistically check acceptance rates for small tractable bit counts, while testing the 32-bit boundary through the pure threshold helper rather than an impractical search.

## Reproduction evidence

```sh
git diff a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0 bbf919d517e693827c81d0f579c74e754399292f -- \
  transcript/src/lib.rs \
  transcript/src/pow.rs
```
