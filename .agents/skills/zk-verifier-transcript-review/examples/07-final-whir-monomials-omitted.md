# Final WHIR monomials were neither serialized nor absorbed

## Classification

- Confirmed historical final-round transcript and proof-serialization bug
- Component: GPU WHIR terminal polynomial reveal
- Security character: incomplete GPU proofs and transcript parity failure; a verifier omitting the same binding would weaken the terminal check
- Fixed by: [`cb3787d`](https://github.com/matter-labs/zksync-airbender/commit/cb3787df94900baed4b675b472c30b78c56d9b2e)
- Vulnerable revision: `1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc`

## Protocol context

WHIR recursion eventually reduces the committed polynomial to a small terminal polynomial. The prover reveals its monomial coefficients, the verifier evaluates that explicit polynomial and checks its consistency with the accumulated claim, and final query/PoW randomness must bind the reveal.

The final reveal is unusual because it is no longer a Merkle cap. It is still a prover message and must satisfy both channels of the protocol implementation: it must be present in the serialized proof and absorbed into the rolling seed before final randomness.

## Intended transcript relation

```text
GPU completes final coefficient vector
copy coefficients to stable host storage
absorb(canonical coefficient vector)
proof.final_monomials <- same coefficient vector
final PoW/query randomness <- squeeze(seed)
verifier evaluates the serialized vector and closes the final claim
```

The coefficient buffer must remain alive until both the transcript callback and proof serialization have consumed it.

## Failure

The GPU final round did neither required operation: it did not absorb the revealed monomial coefficients before final query PoW, and it did not copy them into `proof.final_monomials`. The producer therefore drew its last nonce from a seed independent of the terminal polynomial and emitted a proof missing the object the verifier needed to evaluate.

This is a dual-channel failure. Fixing only the proof field would leave transcript drift; fixing only the absorption would leave an unverifiable proof. It also illustrates that final-round code often has a different grammar from recursive rounds and must not inherit their audit conclusions.

## Failure flow

1. The final polynomial exists only in GPU/device storage.
2. Proof construction advances directly to final PoW.
3. No coefficient vector enters the seed and `proof.final_monomials` remains empty.
4. The canonical verifier both expects the reveal and absorbs it before reconstructing final randomness.
5. Verification fails at serialization, final polynomial consistency, or nonce/challenge parity depending on which check is encountered first.

No false acceptance by the canonical verifier follows from an empty required field. The security lesson is prospective: a verifier implementation that tolerated the missing field or failed to absorb a supplied vector would not bind its terminal polynomial.

## Impact and fix

GPU proofs could not close the WHIR argument and the final nonce diverged from the canonical transcript. The fix schedules asynchronous host readback of the coefficients, keeps the allocation alive, and in stream order commits the coefficients and stores that same vector in the proof before final PoW.

Audit every terminal reveal for four properties: canonical length, proof presence, semantic evaluation/checking, and absorption before the first dependent draw.

## Regression

- Require `proof.final_monomials` to have the protocol-determined nonzero length.
- Compare CPU/GPU transcript events byte-for-byte at the final reveal.
- Mutate one coefficient and require the final PoW seed/nonce and verification result to change.
- Delay host readback or stress stream scheduling to detect use-after-free and early-squeeze bugs.
- Check that the verifier rejects missing, short, long, and noncanonical coefficient vectors.

## Reproduction evidence

```sh
git diff 1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc cb3787df94900baed4b675b472c30b78c56d9b2e -- gpu_prover/src/prover/whir_fold.rs
```
