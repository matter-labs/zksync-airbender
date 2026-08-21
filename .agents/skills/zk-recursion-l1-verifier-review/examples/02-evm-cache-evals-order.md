# Generated EVM batching challenge preceded cache-dependency evaluations

## Classification

- Confirmed reachable Rust/EVM transcript-completeness bug in the generated/test verifier
- Boundary: canonical Rust/GPU GKR transcript → generated Yul verifier transcript
- Component: cache-bearing layer point-claim batching
- Security character: generated verifier used a different transcript from the canonical prover; causal soundness risk exists, but no false-accepting assignment is established
- Fixed by: [`4b0d431`](https://github.com/matter-labs/zksync-airbender/commit/4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8)
- Vulnerable revision: `585e7c9384f83e2d6b98023d8aa5bdd001686faa`

The affected branch had generated contracts, real proof/calldata fixtures, and a
Foundry two-transaction harness. No production deployment or settlement consumer
is established.

## Boundary context

At a cache-bearing GKR layer, the prover sends ordinary final-step evaluations plus extra inner-layer evaluations required by cache dependencies. These form one logical message used to construct the next layer's batched claim.

The canonical transcript hashes `seed || final_step || extras` once and only then draws `next_alpha`. Keccak framing matters: two sequential hashes are not equivalent to one concatenated hash even if the byte multiset is identical.

## Intended transcript contract

```text
message = ordinary_final_step_claims
        || recomputed cache outputs in canonical order
        || prover-provided cache dependency evaluations

seed' = keccak256(seed || message)
next_alpha = field(keccak256(seed'))
next layer claim uses next_alpha
```

Every copied range, count, and ordering must match the proving implementation.

## Failure

Generated Yul copied/absorbed ordinary final-step values, updated the seed, and drew `next_alpha` before copying and absorbing the extra cache-dependency evaluations. It then performed a second Keccak absorb for those extras.

The challenge was therefore causally independent of part of the claim vector and the transcript state diverged from the prover's single-message framing.

## Established failure and conditional soundness flow

1. The canonical prover absorbs `final_step || extras` in one message and draws
   `next_alpha` from that state.
2. The generated verifier absorbed `final_step`, drew, and only then absorbed
   `extras` in a second state transition.
3. Therefore a canonical honest proof reaches different challenges and cannot
   verify under the generated contract.

The old ordering also makes `next_alpha` independent of the extra
prover-controlled evaluations. That is a protocol-level soundness concern, but
history does not establish that the remaining cache equations and WHIR openings
leave enough freedom for a bounded false-accepting assignment. The demonstrated
classification is completeness/transcript incompatibility.

## Impact and fix

The generated challenge failed Rust/EVM transcript parity and did not causally
bind all cache claims. The generator now copies final-step and extra ranges
contiguously into one buffer, performs one
`keccak256(seed || all_values)`, updates the seed, and draws afterward.

Generated transcript code must be audited at the emitted Yul byte-range level. High-level Rust ordering is insufficient when generators split ranges or add hash calls for gas/stack reasons.

## Regression

- Compare event/byte traces and intermediate seeds between Rust prover, Rust verifier, and EVM verifier.
- Mutate one extra evaluation and require `next_alpha` to change.
- Cover zero, one, overlapping, and several cache dependencies.
- Assert one Keccak absorb spans the complete canonical message.
- Test the generated contract, not only the generator's string fragments.

## Reproduction evidence

```sh
git diff 585e7c9384f83e2d6b98023d8aa5bdd001686faa 4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8 -- verifier_evm/src/generator/circuit_yul.rs
```
