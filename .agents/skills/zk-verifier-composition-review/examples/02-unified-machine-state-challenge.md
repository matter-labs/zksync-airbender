# Unified machine-state challenge was not compared

## Classification

- Confirmed historical global-state soundness bug
- Invariant: unified circuit state products and outer public-state contributions use one transcript-derived challenge family
- Component: unified full-statement verifier
- Verifier anchor: `full_statement_verifier/src/unified_circuit_statement.rs` external-challenge equality checks
- Fixed by: [`8ef06cf`](https://github.com/matter-labs/zksync-airbender/commit/8ef06cf8dc63b04e4b309b501d54bb571e86a1a9), PR [#225](https://github.com/matter-labs/zksync-airbender/pull/225)
- Vulnerable revision: `c16b75d2df36af2608fb971c3a75af83cd1c997d`

## Composition context

The unified proof exposes several randomized argument families: RAM, delegation, and machine-state permutation products. The full-statement verifier independently reconstructs expected external challenges from the memory transcript seed and uses them to add public/global boundary contributions before checking final closure.

Each product family needs its own equality edge between the outer challenge and the challenge under which the inner proof computed its accumulator. Equality for the RAM challenge does not imply equality for machine state, even when both originate from one seed.

## Intended invariant

```text
expected = derive(memory_seed, PoW, protocol parameters)
assert expected.memory == proof.memory_challenges[0]
assert expected.delegation == proof.delegation_challenges[0]      # when present
assert expected.machine_state == proof.machine_state_challenges[0]

global_machine_state_product =
    proof.machine_state_accumulator * public_boundary_contribution(expected.machine_state)
assert global_machine_state_product == identity
```

The challenge equality must hold before the inner contribution and outer boundary term are composed.

## Failure

The verifier compared the memory challenge—and conditionally the delegation challenge—but omitted equality between the externally expected machine-state permutation challenge and `proof_output_0.machine_state_permutation_challenges[0]`.

The honest prover derived all three challenge families from the global memory
seed using
`draw_from_transcript_seed_with_state_permutation`. The vulnerable verifier
instead called the older derivation that produced only memory/delegation
challenges. It then used the proof-reported machine-state challenge to encode
the public initial/final PC/timestamp contribution. Thus prover and verifier
could agree internally on an attacker-selected state challenge without that
challenge being the Fiat-Shamir output bound to the global commitments.

## Adversarial flow

1. Fix the unified proof's committed data.
2. Choose the externally supplied machine-state linearization coefficients
   instead of accepting the transcript-derived coefficients.
3. For two distinct state tuples, choose one still-free coefficient so their
   compressed encodings coincide; equivalently, set the coefficient of a
   differing component to zero when the remaining components agree.
4. Prove the local permutation product under that chosen challenge.
5. The outer verifier uses the same proof-reported challenge for its public
   boundary factor, so the final product can close even though the unequal
   state tuples would be detected under a random transcript-derived challenge.

This is the ordinary failure mode of an unbound randomized multiset argument:
the prover can tailor the compression challenge to the false relation rather
than being challenged after commitments are fixed. No hash preimage or
cross-implementation mismatch is needed.

## Impact and fix

The global machine-state check was not guaranteed to be about the same randomized multiset relation as the unified circuit proof. The fix switches to challenge derivation that includes delegation and state permutation and explicitly compares the expected machine-state challenge with the proof output before final accumulation.

Build a challenge-family ledger for composition audits: source seed, derivation function, inner reported value, outer expected value, equality check, and every accumulator consumer. Treat each tuple independently.

## Regression

- Mutate only `machine_state_permutation_challenges[0]` while keeping memory/delegation challenges fixed; require immediate rejection.
- Keep the challenge fixed and mutate the corresponding accumulator; require final closure failure.
- Confirm the equality occurs before any public-boundary contribution is combined.
- Add a test that independently mutates each argument family so one family's check cannot mask another's omission.

## Reproduction evidence

```sh
git diff c16b75d2df36af2608fb971c3a75af83cd1c997d 8ef06cf8dc63b04e4b309b501d54bb571e86a1a9 -- full_statement_verifier/src/unified_circuit_statement.rs
git show c16b75d2df36af2608fb971c3a75af83cd1c997d:circuit_defs/prover_examples/src/unified.rs
```
