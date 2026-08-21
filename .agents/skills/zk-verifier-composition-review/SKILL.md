---
name: zk-verifier-composition-review
description: Defensively audit one named cross-circuit, cross-chunk, or global verifier invariant—such as RAM/permutation closure, PC/timestamp continuity, delegation, LogUp aggregation, padding, chunk coverage, or public-state composition—across the exact proof participants needed to establish it. Use for focused composition reviews of Rust, recursive, generated, or prover-first implementations; do not expand one invariant into a whole proof-system audit.
---

# Focused Cross-Circuit and Global-Composition Review

Audit one global invariant horizontally across all of its required participants.
The bounded target is the invariant, not one convenient file and not every
global argument in the repository.

## Require one composition target

Resolve:

- one invariant: memory/RAM, PC and timestamp, delegation/precompiles, lookup
  aggregation, padding neutrality, chunk coverage, setup identity, or another
  explicitly named global relation;
- its authoritative verifier/aggregator entrypoint;
- the exact proof classes, circuit families, chunk types, and injected boundary
  contributions that participate;
- one version, proof-system instance, feature/security mode, and final consumer.

If the user supplied no invariant, ask which global invariant to audit. Do not
select all of them. Include several participants only because one invariant
cannot be established without them; keep participant-specific coverage.

Default to verifier outputs and aggregation code, where contributions converge.
Read circuit and prover code to recover tuple meaning, honest contribution
format, and missing specification. If the verifier is not yet available and the
user targets the prover, produce a provisional composition contract and list all
acceptance checks that remain unverified.

## Transcript is part of the invariant

Every probabilistic global argument has a local Fiat-Shamir obligation. Rebuild
the transcript slice that fixes its commitments, shared challenges, accumulator
claims, counts, and final equality. Do not assume a separate transcript review
made protocol-specific ordering correct. If a transcript artifact exists,
consume and verify it; otherwise produce the relevant rows here.

## Read the applicable references

Always read:

- [cross-circuit and aggregation](../zk-verifier-review/references/cross-circuit-and-aggregation-expanded.md)
- [Fiat-Shamir transcript](../zk-verifier-review/references/fiat-shamir.md)

For matching targets, read:

- [Airbender architecture](../zk-verifier-review/references/airbender-verifier-architecture.md)
- [Airbender snapshot profile](../zk-verifier-review/references/airbender-gkr-v1-profile.md)
- optional circuit-side contracts from `../zk-circuit-review/references/`:
  `global-arguments-scope.md`, `memory-and-ram.md`, `lookups-and-logup.md`,
  `padding.md`, `public-io-binding.md`, and `gkr-wiring-and-aggregation.md`.

## Workflow

1. State the aggregate invariant algebraically and in plain language. Identify
   what an accepting verifier claims after composition.
2. Enumerate all producers, consumers, neutral/empty contributors, verifier-
   injected terms, initialization/teardown terms, and final checks. Search call
   sites before declaring a family absent.
3. Build the contribution matrix below. Trace every tuple field from local
   committed data through the per-proof output into the global accumulator.
4. Establish challenge provenance and identity field-by-field. Check commitment
   timing, deferred challenge re-derivation, transcript grouping, equality of all
   challenge components, and dominance of the final comparison over every exit.
5. Check identities and type separation: circuit/setup caps, family tags,
   delegation type, chunk size, security level, version, program identity, and
   public input/output context.
6. Check counts and degenerate cases: zero contributors, empty families,
   singleton chunks, all-padding chunks, maximum cycles/elements, multiplicity
   wraparound, timestamp wraparound, duplicates, omissions, and reordering.
7. Trace boundary state. For machine execution, prove the chain from initial
   PC/register/timestamp state through chunk boundaries to final state rather
   than relying on names such as “global memory.”
8. Trace the selected invariant to its final consumer: aggregate verifier output,
   recursive statement, registry state, or settlement decision. Stop at that
   handoff and record the next layer as a coverage dependency.
9. Search for a single malicious participant that can make an unbalanced or
   malformed contribution while all other participants remain honest. Then
   search aggressively for later checks that close the freedom.

## Required artifacts

### Invariant dossier

```text
target invariant; exact accumulator/equality; challenge tuple; element/count
bounds; initial/final terms; participant set; final consumer; assumptions
```

### Contribution matrix

| Participant | Activation/count | LHS/read contribution | RHS/write contribution | Challenges | Setup/type binding | Padding/empty behavior |
|---|---|---|---|---|---|---|

### Challenge-continuity table

| Challenge component | Commitments fixed first | Derived/re-derived at | Supplied to participants | Compared where | Missing participant/path |
|---|---|---|---|---|---|

### Boundary-state map

Record verifier-injected genesis/teardown terms, per-chunk state, reordering
rules, and the exact final public state.

## Evidence gate

Confirm a soundness finding only with the intended global invariant, exact
participant freedom, all local and aggregate checks, a reachable bounded
symbolic composition that passes while the invariant is false, and impact on the
final accepted statement. A missing local circuit relation belongs in a circuit
review unless it manifests as an unchecked composition interface. Keep
unresolved participant coverage as a dependency, not a finding.

If active producer or aggregation code is defective but no consuming proof
path and no concrete honest-proof rejection path is established, classify it
as an **implementation-only defect**, not soundness or completeness. If the
broken value is observable only through a callback, feature, or participant
with no connected consumer, classify it as **latent** and state the exact
activation condition. Do not infer a missing participant merely because stale
metadata could hypothetically control orchestration.

Do not discard a concrete composition defect solely because its producer,
aggregator, feature, or artifact is not currently connected. Report it
separately as a **latent finding** when the broken invariant and activation
condition are exact, while withholding deployed severity and present-acceptance
claims. Mere missing integration evidence or a speculative future participant
remains a dependency or lead. Do not misclassify reachable completeness or
robustness failures as latent.

## Deliverable

Report one invariant, its complete necessary participant set, confirmed
findings, leads, closures, artifacts, and explicit exclusions. Never imply that
reviewing memory also covered delegation, lookup aggregation, padding, recursion,
or settlement unless each was separately selected.

Keep the work authorized, source-local, read-only, and defensive. Do not build
malicious provers or operational proof forgeries.
