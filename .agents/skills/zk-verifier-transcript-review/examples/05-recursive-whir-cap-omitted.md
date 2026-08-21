# Recursive WHIR oracle cap was not absorbed

## Classification

- Confirmed historical GPU transcript-omission bug
- Component: recursive WHIR oracle commitment handoff
- Security character: confirmed honest-proof rejection/completeness failure;
  the canonical verifier still bound the cap
- Fixed by: [`66ccc73`](https://github.com/matter-labs/zksync-airbender/commit/66ccc73e02d3913dec0298856cc334084836da9d)
- Vulnerable revision: `e865551a08068caa4dc5be7e720a57198fe23622`

## Protocol context

Each WHIR recursive round folds the current claim, commits a smaller Reed-Solomon oracle, and uses the new oracle cap to derive the next out-of-domain point and query phase. The cap is the prover's binding message for that oracle. Every later challenge used to test it must depend on the fully materialized cap.

The GPU implementation constructs caps asynchronously. Correct protocol order is therefore also a device/host scheduling invariant: the transcript callback must run after all cap digests are populated and before any callback that consumes the next OOD or query randomness.

## Intended transcript relation

For every recursive round, independently:

```text
GPU builds intermediate oracle and Merkle tree
GPU/host materializes complete cap
proof.intermediate_whir_oracles[round].commitment <- cap
absorb(cap)
ood_point <- squeeze(seed)
...
query PoW/indexes and delinearization <- later squeezes
```

The fact that the base round performs this order does not cover recursive iterations.

## Failure

The GPU prover materialized each intermediate WHIR Merkle cap and stored it in the proof, but failed to add it to the rolling seed. It proceeded to derive the next OOD point, query PoW/query indices, and delinearization challenge from the pre-cap seed.

This is the most important kind of transcript omission: a prover-controlled commitment existed in serialized proof data and was semantically verified, yet it was absent from the challenges intended to test the committed oracle. Code review focused only on proof struct population could therefore miss it.

## Failure flow

1. GPU finishes a recursive oracle and exposes its cap.
2. A stream-ordered callback copies the cap into the proof object.
3. No transcript update occurs.
4. The prover derives the next OOD point and query phase as if the cap had not been sent.
5. The canonical CPU/recursive verifier absorbs the cap and derives different randomness.

Against the canonical verifier this manifests as honest GPU proof rejection after the first affected recursive step. If a verifier port copied the same omission, the stronger consequence would be an unbound oracle commitment. The historical fix demonstrates the producer-side parity bug; it does not by itself prove that the canonical verifier accepted forged proofs.

## Impact and fix

Every draw after the first recursive cap diverged: the next OOD point, query PoW seed and indices, delinearization challenge, and later round state. The fix invokes the shared cap-absorption routine in the existing ordered callback, after cap population and before the next OOD randomness is uploaded.

For asynchronous implementations, audit a three-way relation for every message: device completion, proof serialization, and transcript absorption. Two of the three being ordered correctly is insufficient.

## Regression

- Emit an event trace for every round and require `cap complete -> proof write + absorb(cap) -> squeeze(OOD)`.
- Mutate one digest of only a recursive cap and require every downstream challenge to change.
- Compare CPU and GPU seeds immediately after each cap, rather than waiting for final verification failure.
- Exercise at least two recursive rounds; a one-round proof never reaches the repeated path.
- Run under delayed GPU callbacks to expose ordering assumptions.

## Reproduction evidence

At the vulnerable revision, generated `verify_whir` calls the internal-round
verifier, which reads and commits the intermediate cap before drawing
`ood_point`. The GPU prover skipped that commit. The historical commit message
also records the resulting CPU/GPU divergence in the next OOD, PoW/query
indexes, and delinearization draws:

```sh
git diff e865551a08068caa4dc5be7e720a57198fe23622 66ccc73e02d3913dec0298856cc334084836da9d -- gpu_prover/src/prover/whir_fold.rs
git show e865551a08068caa4dc5be7e720a57198fe23622:verifier_generator/src/whir/rounds.rs
```
