# Prover-side merged L1 transcript omitted future terminal-state framing

## Classification

- Producer-parity history: exact latent prover transcript defect in merged-and-packed mode
- Boundary: public terminal machine state → internally derived memory challenges in merged-and-packed mode
- Component: `CommitmentMode::MergedAndPackedMemoryAndWitness`
- Security character: memory challenges omitted state intended for a future L1 closure, but the contemporaneous contract did not accept that state
- Fixed by: [`f15c643`](https://github.com/matter-labs/zksync-airbender/commit/f15c64359f852837c9ffe4fe368a62f34b6e3c89)
- Vulnerable revision: `b75be7bbecc17860dac85a6d875887a7e7fb1396`

## Boundary context

The merged-and-packed L1 proof instance re-derives memory/delegation challenges inside the proof pipeline rather than receiving them from an outer full-statement verifier. Its global memory closure includes public machine-state reads/writes for 32 registers plus final PC/timestamp.

Those boundary values are part of the statement sampled by the permutation argument. They must be fixed before the challenges used to compress their tuples are drawn.

## Intended transcript contract

Before setup commitments and external argument challenges, absorb canonically:

```text
for registers 0..31:
    register value || last-access timestamp low || timestamp high
final PC || final timestamp low || final timestamp high
inits/teardowns window identifiers
setup and relevant commitments
then derive/grind external challenges
```

The verifier/L1 consumer must reconstruct the identical order and encoding from authenticated public input.

## Failure

The merged-and-packed mode re-derived external memory challenges without including the final register values/timestamps or final PC/timestamp in its transcript input. Those values later supplied the machine-state contribution used to close the same permutation.

Consequently the random compression coefficients were independent of a verification-relevant public boundary chosen by the statement/prover path.

## Why excluded from verifier examples

At the vulnerable revision, `CommitmentMode::MergedAndPackedMemoryAndWitness`
had no final-state fields at all, and the contemporaneous `verifier_evm/gkr.sol`
transcript consumed only I/T top bits and setup/memory caps. No final register,
PC, or timestamp values crossed the contract's accepted-statement boundary.
Thus the omission was a producer-side future-integration defect, not a latent
verifier defect or a false claim accepted by that contract.

## Adversarial flow

1. Fix commitments and derive memory challenges from a transcript omitting final state.
2. Learn those challenges.
3. Choose or alter terminal register/PC/timestamp tuples afterwards within any remaining proof freedom.
4. Target the compressed machine-state contribution/global product under known randomness.
5. Present the resulting terminal state as the L1-visible statement.

The complete acceptance impact depends on how the generated/EVM verifier obtains and binds these fields. The protocol ordering is nevertheless invalid wherever the final state remains prover-controlled until after the challenge.

## Impact and fix

The L1-oriented memory argument would not have cryptographically bound terminal
public state when that state was connected. The fix extends the commitment mode
with final state, serializes 32 register triples and one PC/timestamp triple, and
absorbs them before I/T window/setup data and challenge derivation.

An outer recursive proof does not repair a missing inner statement binding unless it authenticates both the state and the exact challenge derivation that included it.

## Regression

- Mutate every terminal value/timestamp limb independently while preserving commitments; require the external challenge seed to change.
- Compare native merged-mode and L1 verifier transcript bytes.
- Reject noncanonical timestamp limb encodings.
- Assert terminal-state absorption precedes every memory/delegation challenge/PoW draw.
- Verify the final settlement output exposes the same state that entered the transcript.

## Reproduction evidence

```sh
git diff b75be7bbecc17860dac85a6d875887a7e7fb1396 f15c64359f852837c9ffe4fe368a62f34b6e3c89 -- prover/src/gkr/prover/mod.rs
```
