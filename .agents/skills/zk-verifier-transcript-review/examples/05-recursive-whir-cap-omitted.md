# Recursive WHIR oracle cap was not absorbed

## Classification

- Confirmed historical GPU transcript-omission bug
- Component: recursive WHIR rounds
- Fixed by: [`66ccc73`](https://github.com/matter-labs/zksync-airbender/commit/66ccc73e02d3913dec0298856cc334084836da9d)
- Vulnerable revision: `e865551a08068caa4dc5be7e720a57198fe23622`

## Failure

The GPU prover materialized and stored each intermediate WHIR Merkle cap but did not add it to the rolling transcript before the next OOD point, query PoW, query indices, and delinearization challenge.

## Impact and fix

The cap was not bound by challenges intended to authenticate its oracle, and GPU proofs diverged from the canonical verifier. The fix absorbs the fully populated cap in the existing ordered callback before any later draw.

## Regression

Record `absorb(cap) -> squeeze(OOD)` for every recursive round and mutate one cap digest to ensure all downstream challenges change.

```sh
git diff e865551a08068caa4dc5be7e720a57198fe23622 66ccc73e02d3913dec0298856cc334084836da9d -- gpu_prover/src/prover/whir_fold.rs
```
