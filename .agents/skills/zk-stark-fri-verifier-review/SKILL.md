---
name: zk-stark-fri-verifier-review
description: Defensively audit one named legacy AIR/STARK verifier component, quotient or DEEP-ALI reduction, FRI verifier phase, generated verifier slice, or immediate STARK-to-FRI handoff. Use for deep theory-guided reviews of Rust, generated, recursive, or explicitly requested prover implementations and historical Airbender versions; require one fingerprinted version, entrypoint, and phase rather than a repository-wide legacy audit.
---

# Focused AIR, DEEP-ALI, and FRI Verifier Review

Audit one concrete legacy STARK reduction and the protocol-specific transcript
ordering that makes it sound. Do not project current GKR assumptions onto a
historical verifier.

## Require a bounded target and focus

Resolve one versioned proof-system instance and one primary focus:

- one AIR constraint-composition or quotient path;
- one boundary/transition-domain family;
- one quotient splitting/recomposition step;
- one OOD/DEEP-ALI batching seam;
- one FRI commitment, folding, query, Merkle, or terminal round;
- one small adjacent chain in a concrete generated verifier.

Fingerprint tag/commit, entrypoint, field/extension, domain, transcript/hash,
trace and quotient degree bounds, blowup, FRI schedule, security mode, generated
artifact, and caller. If the target is ambiguous, ask. Do not review every
historical tag or every constraint group in one run.

Default to the verifier. Use the prover to recover honest oracle order,
evaluation layout, and intended deviations after reconstructing verifier
behavior. If only a prover is ready and explicitly targeted, write a provisional
verification contract and mark acceptance conclusions as pending.

## Mandatory local transcript contract

Reconstruct the selected interactive protocol before Fiat-Shamir. Check that
trace/setup/auxiliary/quotient/FRI commitments, claimed evaluations, round
oracles, final polynomial, PoW nonce, and query openings precede the challenges
that randomize or select them. The phase specialist owns these rows even when a
separate transcript audit exists.

## Read the applicable references

Always read:

- [legacy AIR, DEEP-ALI, and FRI](../zk-verifier-review/references/stark-deep-fri.md)
- [Fiat-Shamir transcript](../zk-verifier-review/references/fiat-shamir.md)

For detailed specification recovery, read
[normative sources](../zk-verifier-review/references/normative-sources-expanded.md).
Use a current Airbender profile only as a migration contrast; fingerprint the
historical tag from its own entrypoint and source.

## Workflow

1. Recover the exact AIR statement: trace/setup/auxiliary columns, row domains,
   transition offsets, constraint degrees, public/boundary values, and committed
   oracles.
2. Enumerate every constraint group and its activation/vanishing denominator.
   Check first, last, last-two, shifted previous/next, padding, and exceptional
   domains separately.
3. Trace random constraint composition: commitment timing, coefficient draw,
   item order, signs, degree effects, omitted/duplicate constraints, and any
   challenge reuse across logically independent relations.
4. Verify quotient construction, expected degree, part count/order, splitting,
   recomposition, and every evaluation used at the OOD point and shifted points.
5. For DEEP/ALI, inventory every trace, setup, auxiliary, quotient, and shifted
   evaluation in the batch. Prove the batching challenge is timely and the
   composition polynomial opened by FRI is exactly the one implied by the
   quotient identity.
6. For FRI, trace oracle caps, fold challenges, domains/cosets, arities, query
   indices, bit-reversal, leaf/path formats, terminal polynomial degree and
   evaluation, PoW, and proof exhaustion.
7. At the DEEP/FRI seam, prove equality of composition claim, sampling point,
   source polynomial inventory, coefficient order, domains, and authenticated
   openings.
8. Audit migration residue: stale helpers, changed field encodings, transcript
   padding, Merkle ordering, query extraction, domain generators, and feature-
   selected verifier paths.
9. Record local error terms for constraint batching, quotient/OOD sampling,
   DEEP combination, FRI proximity, queries, and grinding. Hand the combined
   accounting to the soundness-budget specialist.

## Required artifacts

### Version and phase fingerprint

```text
tag/commit; entrypoint; generated artifact; field/extension; transcript;
domains/degrees; blowup/FRI schedule; selected phase; adjacent handoffs
```

### Constraint/quotient inventory

| Group | Intended row domain | Degree | Random coefficient/order | Quotient part/evaluation | Checked/opened where |
|---|---|---|---|---|---|

### DEEP/FRI claim chain

| Step | Prover object | Transcript timing | Required identity | Outgoing claim/oracle | Authentication/final check |
|---|---|---|---|---|---|

### Local transcript rows and soundness terms

Record all selected-phase challenges and quantitative assumptions. Do not claim
whole-system security bits from a local phase.

## Evidence gate

Confirm a soundness finding only with the exact historical invariant, prover
freedom, all constraint/transcript/opening checks, reachable tag/configuration,
and a bounded symbolic accepting flow for a false AIR or low-degree claim. Keep
it non-executable. Separate completeness, stale-code, and specification issues.

## Deliverable

Report the selected historical version, phase, immediate handoffs, findings,
leads, closures, inventories, local transcript, error terms, and every unreviewed
constraint group, oracle class, FRI round, or aggregation dependency.

Keep the work authorized, source-local, read-only, and defensive. Do not build
proof forgeries or operational malicious provers.
