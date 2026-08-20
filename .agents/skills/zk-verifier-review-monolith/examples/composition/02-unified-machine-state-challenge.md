# Unified machine-state challenge was not compared

## Classification

- Confirmed historical global-state soundness bug
- Invariant: unified circuit state products and outer public-state contributions use one transcript-derived challenge family
- Component: unified full-statement verifier
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

It then combined a proof-reported machine-state accumulator with outer logic whose challenge provenance was not connected to the proof. The existence of a final product equality did not close this gap: a product computed under one random encoding has no sound relation to a boundary contribution computed under another.

## Adversarial flow

1. Construct the inner unified proof and its machine-state accumulator under a chosen or otherwise different challenge value.
2. Pass local verification under the challenge carried/derived inside that proof path.
3. Let the outer verifier independently derive the expected challenge used for public state.
4. Because no equality is enforced, both values can enter different sides of the composition.
5. Exploit the extra freedom in the proof output/accumulator relation to target the outer closure without proving continuity under the public statement's challenge.

The exact forgery depends on which proof outputs are constrained inside the unified verifier, but the missing cross-boundary equality invalidates the global-state soundness argument on its face.

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
```
