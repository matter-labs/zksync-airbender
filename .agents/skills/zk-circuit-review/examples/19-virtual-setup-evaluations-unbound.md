# GKR virtual-setup claims were not checked against their definitions

## Classification

- Confirmed historical proof-system soundness bug
- Components: GKR verifier generator and virtual setup polynomials
- Bug class: deterministic setup oracle accepted without recomputation
- Fixed by: [`287ba6d`](https://github.com/matter-labs/zksync-airbender/commit/287ba6d1086fdc5efc1d361ac779b9ad20de0bc8), PR [#282](https://github.com/matter-labs/zksync-airbender/pull/282)
- Vulnerable revision for reproduction: `b55f37d69593d0cf84b656a42eb8a3c4262d2a2a`

## Intended relation

`VirtualSetup` polynomials represent deterministic tables that are not ordinary prover-committed witness columns: 16-bit range values, timestamp-range values, and low/high initialization-address values. At the final GKR opening point, the verifier must compute each multilinear evaluation in closed form and compare it with the corresponding layer-zero claim.

## Vulnerable relation

The prover populated and used these polynomials, but generated verifiers did not derive their expected evaluations. Their layer-zero claims entered GKR checks without a final equality to the fixed polynomial definition.

## Security impact

A lookup or initialization relation could be proved relative to arbitrary claimed setup evaluations rather than the protocol's fixed range and address tables. The sumcheck could remain internally consistent while failing to establish the circuit relation against the intended deterministic setup.

## Fix

Verifier generation now identifies every virtual-setup address in the canonical layer-zero layout, emits closed-form evaluation helpers for all supported variants, and compares them with `prev_claims`. A mismatch returns `GkrVirtualSetupEvalMismatch`; inconsistent low/high initialization variants fail during generation.

## Audit lesson

Classify every leaf oracle by who commits or defines it. Witness and setup Merkle openings, transcript values, and closed-form virtual polynomials need different binding checks; being present in a GKR address list does not authenticate the leaf.

## Regression test

- For random verifier points, compare each generated closed-form helper with a direct multilinear evaluation of the materialized virtual polynomial.
- Enumerate `VirtualSetupPoly` variants and require verifier generation to handle each one explicitly.
- Verify valid fixtures for range-check and initialization circuits and assert their virtual claims equal independently computed values.

## Reproduction evidence

```sh
git diff b55f37d69593d0cf84b656a42eb8a3c4262d2a2a 287ba6d1086fdc5efc1d361ac779b9ad20de0bc8 -- \
  verifier_generator/src/gkr/mod.rs \
  verifier_common/src/errors.rs
```
