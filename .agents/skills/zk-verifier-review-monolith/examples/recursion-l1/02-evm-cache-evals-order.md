# EVM batching challenge preceded cache-dependency evaluations

## Classification

- Confirmed historical L1 Fiat-Shamir ordering bug
- Boundary: canonical Rust/GPU GKR transcript → generated Yul verifier transcript
- Component: cache-bearing layer point-claim batching
- Security character: next-layer batching coefficient did not bind every prover-supplied evaluation
- Fixed by: [`4b0d431`](https://github.com/matter-labs/zksync-airbender/commit/4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8)
- Vulnerable revision: `585e7c9384f83e2d6b98023d8aa5bdd001686faa`

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

## Adversarial flow

1. Fix ordinary final-step claims and let the contract derive `next_alpha`.
2. Choose extra dependency evaluations after learning that coefficient.
3. Use their remaining freedom to target the randomized next-layer relation.
4. Absorb the chosen values only after the dependent challenge is fixed.

Even when an algebraic cancellation is not reachable for a particular cache graph, the L1 verifier did not implement the canonical proof transcript and rejected honest proofs. The ordering violation itself is soundness-critical because these are prover-controlled inputs to the batch.

## Impact and fix

The on-chain challenge did not bind all cache claims and failed Rust/EVM transcript parity. The generator now copies final-step and extra ranges contiguously into one buffer, performs one `keccak256(seed || all_values)`, updates the seed, and draws afterward.

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
