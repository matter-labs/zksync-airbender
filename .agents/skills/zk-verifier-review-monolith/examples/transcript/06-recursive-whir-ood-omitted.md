# Recursive WHIR OOD value was not absorbed

## Classification

- Confirmed historical GPU transcript-omission bug
- Component: recursive WHIR OOD phase
- Fixed by: [`1b2f74f`](https://github.com/matter-labs/zksync-airbender/commit/1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc)
- Vulnerable revision: `66ccc73e02d3913dec0298856cc334084836da9d`

## Failure

Recursive rounds stored the prover's OOD evaluation in the proof but omitted `commit_field_els(seed, [ood_value])` before query PoW and delinearization. The base round already used the correct order.

## Impact and fix

Later randomness did not bind a verification-relevant claimed evaluation. The fix absorbs the OOD value in the same stream-ordered callback that records it. Audit repeated protocol rounds independently; a correct base round does not prove recursive-round parity.

## Regression

Mutate only a recursive OOD value and require the following PoW seed and delinearization challenge to change.

```sh
git diff 66ccc73e02d3913dec0298856cc334084836da9d 1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc -- gpu_prover/src/prover/whir_fold.rs
```
