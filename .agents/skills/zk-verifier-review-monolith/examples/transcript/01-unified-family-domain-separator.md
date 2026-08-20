# Unified circuit family was not transcript-bound

## Classification

- Confirmed historical Fiat-Shamir statement-binding bug
- Component: unified full-statement verifier and universal verifier-binary dispatch
- Security character: cross-context replay / semantic-aliasing risk, conditional on compatible proof layouts
- Fixed by: [`7bfd63b`](https://github.com/matter-labs/zksync-airbender/commit/7bfd63b42fc56b5b44c0c24200e930259d4eb95b)
- Vulnerable revision: `745cfa076989dbd1e430c422be9803c2bdb8c2d2`

## Protocol context

The full-statement verifier derives one rolling seed from public state and the commitment caps of every proof participant. Challenges derived from that seed are later used by the individual circuit verifiers and by the global memory/delegation closure. The universal verifier binary can dispatch to different statement families, so the same byte representation may acquire different semantics depending on the selected family.

The family identifier is therefore part of the statement, not merely host-side dispatch metadata. It must enter the seed before any proof-family-dependent commitment or challenge is interpreted.

## Intended transcript relation

For a unified statement the prefix should have the shape:

```text
seed_0 = H(public statement and final-state prefix)
seed_1 = H(seed_0 || pad(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX))
seed_2 = H(seed_1 || first unified-circuit proof data)
...
```

Changing only the family must change every challenge downstream of `seed_1`.

## Failure

The verifier entered the unified-circuit proof loop without first absorbing `REDUCED_MACHINE_CIRCUIT_FAMILY_IDX`. It bound the commitment and proof bytes, but not the circuit-family interpretation under which those bytes were parsed and verified. The selected verifier operation lived outside the Fiat-Shamir state.

Consequently, two statement modes with a compatible serialized prefix could reach the same seed from the same public data and proof bytes. Local polynomial and Merkle checks do not repair this omission: they prove the claims associated with the challenges they receive, but they do not establish that those challenges were derived for the intended circuit family.

## Adversarial flow

1. Obtain or construct a proof stream accepted under family `A`.
2. Present the same transcript-relevant bytes through family `B`'s entrypoint.
3. If the two modes accept a compatible layout and parameters, both derive identical challenges because the family choice was never absorbed.
4. The verifier then interprets the same commitments and claims under a different statement language without a cryptographic domain boundary.

This example establishes the missing binding. Whether a concrete cross-family proof reaches acceptance additionally depends on parser, setup, and parameter compatibility; the bug should not be overstated as unconditional replay across every family.

## Impact and fix

The omission made circuit-family identity unauthenticated transcript context and created a cross-mode replay surface. The fix absorbs a padded family identifier immediately before the per-circuit proof loop, so the first and all subsequent challenges differ across statement families.

Audit every verifier entrypoint for circuit family, protocol/version, verifier-key or setup identity, security mode, program identity, and recursion role. A host-side branch or Rust enum comparison is not a transcript binding unless its canonical representation is absorbed before dependent randomness.

## Regression

- Hold public inputs, caps, and proof bytes fixed; mutate only the family/mode and require the pre-proof seed to differ.
- Attempt a cross-mode replay using the most serialization-compatible pair of entrypoints and require rejection.
- Assert the tag is absorbed exactly once and before the first family-dependent squeeze.
- Include the zero-proof or empty-family path so an early return cannot bypass domain separation.

## Reproduction evidence

The scoped historical diff shows the missing padded tag being inserted before the proof loop:

```sh
git diff 745cfa076989dbd1e430c422be9803c2bdb8c2d2 7bfd63b42fc56b5b44c0c24200e930259d4eb95b -- full_statement_verifier/src/unified_circuit_statement.rs
```
