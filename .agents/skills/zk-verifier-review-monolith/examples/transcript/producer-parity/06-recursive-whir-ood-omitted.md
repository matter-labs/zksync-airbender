# Recursive WHIR OOD value was not absorbed

## Classification

- Producer-parity history: confirmed GPU transcript-omission bug
- Component: recursive WHIR OOD-claim handoff
- Security character: confirmed honest-proof rejection/completeness failure;
  a verifier sharing the omission would fail to bind a claimed evaluation
- Fixed by: [`1b2f74f`](https://github.com/matter-labs/zksync-airbender/commit/1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc)
- Vulnerable revision: `66ccc73e02d3913dec0298856cc334084836da9d`

## Protocol context

Once the transcript-derived OOD point is known, the prover sends the evaluation of the committed folded polynomial at that point. That value is not a verifier challenge; it is a prover-controlled claim. Before the verifier derives query positions or a random coefficient that combines the OOD relation with other checks, it must absorb the claimed value.

This gives two separate causal edges in one WHIR round:

```text
oracle cap -> OOD point
oracle cap + OOD point + claimed OOD value -> query/delinearization randomness
```

Absorbing the cap correctly does not compensate for omitting the subsequent claimed evaluation.

## Failure

The recursive GPU rounds stored the OOD evaluation in the proof but omitted `commit_field_els(seed, [ood_value])` before deriving query PoW, query indices, and delinearization randomness. The initial/base path already used the correct order, leaving only the repeated recursive path inconsistent.

The proof object thus contained a verification-relevant field element that was never represented in the producer's transcript state. This is precisely why audits must enumerate every parsed/sent field and identify its first dependent challenge rather than assume all proof fields are absorbed by a generic serializer.

## Failure flow

1. The cap is committed and an OOD point is drawn correctly.
2. The GPU evaluates the polynomial and writes `ood_value` into the proof.
3. It skips absorbing that value.
4. It grinds/draws queries and draws the delinearization coefficient from the old seed.
5. The canonical verifier absorbs the parsed `ood_value` and follows a different random path.

The historical consequence is GPU proof incompleteness against the canonical verifier. In any verifier port that repeated the omission, the prover could choose the OOD claim without affecting the later batching/query randomness that is supposed to constrain it.

## Impact and fix

Later query and delinearization challenges were independent of the recursive OOD claim on the GPU path and therefore disagreed with the canonical implementation. The fix absorbs the value inside the same stream-ordered callback that records it in the proof, before any dependent draw.

Repeated protocol rounds deserve independent transcript tables. A correct base round is weak evidence for a loop body implemented by separate callbacks, kernels, or generated code.

## Regression

- Mutate only one recursive OOD value and require the following PoW seed, query indices, and delinearization challenge to change.
- Compare producer and verifier seeds after each OOD claim.
- Exercise a proof with multiple recursive rounds and identify values by round index in the event trace.
- Assert `proof write` and `absorb` consume the same canonical field encoding in the same callback.

## Reproduction evidence

The same-revision generated verifier reads the recursive OOD value, commits its
four extension-field words, and only then verifies PoW and draws queries. The
GPU producer performed those events in the opposite effective transcript:

```sh
git diff 66ccc73e02d3913dec0298856cc334084836da9d 1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc -- gpu_prover/src/prover/whir_fold.rs
git show 66ccc73e02d3913dec0298856cc334084836da9d:verifier_generator/src/whir/rounds.rs
```
