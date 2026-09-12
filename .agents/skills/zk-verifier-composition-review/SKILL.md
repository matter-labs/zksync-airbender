---
name: zk-verifier-composition-review
description: Defensively audit cross-circuit, cross-chunk, and global verifier invariants—such as RAM/permutation closure, PC/timestamp continuity, delegation, LogUp aggregation, padding, chunk coverage, or public-state composition—across the exact verifier outputs and proof participants needed to establish them. Use for one named invariant or a bounded verifier surface whose invariants must be reviewed independently; do not silently treat one selected invariant as coverage of the others.
---

# Focused Cross-Circuit and Global-Composition Review

Audit one global invariant horizontally across all of its required participants.
The bounded target is the invariant, not one convenient file and not every
global argument in the repository.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

## Resolve the composition target and coverage set

Resolve:

- either one named invariant or one bounded verifier/aggregator surface;
- every independent composition invariant present in that surface: memory/RAM,
  PC and timestamp, delegation/precompiles, lookup aggregation, padding
  neutrality, chunk coverage, setup identity, or another global relation;
- its authoritative verifier/aggregator entrypoint;
- the exact proof classes, circuit families, chunk types, and injected boundary
  contributions that participate;
- one version, proof-system instance, feature/security mode, and final consumer.

If the user named one invariant, audit it deeply without claiming coverage of
neighboring invariants. If the user supplied a bounded verifier surface or a
domain-wide evaluation, first inventory its independent composition invariants,
then audit them **one at a time as separate proof obligations**. Finishing one
does not authorize stopping while another in-scope invariant remains. This
separation is for depth and clean reasoning, not for discarding other required
coverage. Include several participants only when an invariant cannot be
established without them; keep participant-specific coverage.

Do not select the easiest or most salient invariant and mistake it for the
whole composition review. Timestamp capacity, for example, does not cover
delegation authorization, setup identity, chunk inclusion, accumulator
closure, padding, PC continuity, or terminal-state binding. Maintain a coverage
ledger of every in-scope invariant and mark each reviewed, closed, finding, or
explicitly deferred.

Start from verifier outputs and aggregation code, where contributions converge.
Read circuit or prover code only after the accepted composition relation is
mapped, and only to recover tuple meaning, proof framing, or missing
specification. If the verifier or final aggregation consumer is not available,
this skill cannot complete a composition audit; do not substitute a prover-first
contract.

### Verifier-first search discipline

Begin at each final verifier/aggregator equality and walk backward through only
the authenticated outputs that feed it. Search all verifier-side entrypoints,
helpers, generated verifier calls, recursive consumers, and final acceptance
paths needed to establish the selected invariant; a convenient anchor file is a
starting point, not the audit boundary. Spend context on verifier contribution
accounting, participant identity, boundary injections, and success exits. Open a
circuit or prover implementation only when one already-identified verifier
field lacks semantics, and stop after resolving that field. A producer-side
missing or malformed contribution is not a composition finding when the
verifier's accepted global invariant rejects it.

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
7. Audit iteration symmetry and every index class. For each loop over proofs,
   chunks, circuit families, or recursive steps, establish that authorization,
   setup/type binding, challenge checks, contribution accounting, and final
   validation dominate **every accepting iteration**. Inspect every condition
   involving an index, count, first/last flag, empty/non-empty case, or circuit
   sequence. Test at least singleton, first, middle, and last iterations when
   they exist. Treat a check guarded by `index == 0`, `index > 0`, `count > 0`,
   first/last status, or a similar special case as an obligation to prove why
   the unchecked iterations are safe; never summarize a family as fully bound
   from observing only its first proof.
8. Check honest-output semantics before crediting an apparent authorization or
   ordering check. Never infer that a verifier field is live, constrained, or
   meaningful from its name. For every proof output compared with a loop index,
   counter, family/type value, boundary marker, or expected sequence, trace how
   the honest format and generated verifier populate it and classify it as
   derived, constrained, constant, placeholder, or legacy. Simulate honest
   singleton, second, and later iterations. A comparison that appears to harden
   ordering can instead reject every valid multi-item proof when its input is a
   fixed compatibility value. Record this as a completeness defect even when it
   creates no false-acceptance path.
9. Trace boundary state. For machine execution, prove the chain from initial
   PC/register/timestamp state through chunk boundaries to final state rather
   than relying on names such as “global memory.”
10. Trace the selected invariant to its final consumer: aggregate verifier output,
   recursive statement, registry state, or settlement decision. Stop at that
   handoff and record the next layer as a coverage dependency.
11. Search for a single malicious participant that can make an unbalanced or
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

If only producer, circuit, replay, callback, or proof-assembly code is defective
and the selected verifier rejects its output, classify it as **producer parity**
and keep it outside primary findings. A verifier/aggregator helper or emitted
verifier defect with no selected consumer may be **implementation-only** or
**latent** under the rule below. Do not infer a missing participant merely
because stale producer metadata could hypothetically control orchestration.

Do not discard a concrete verifier-side composition defect solely because its
aggregator, feature, or artifact is not currently connected. Report it
separately as a **latent finding** when the defective verifier relation and
activation condition are exact, while withholding deployed severity and
present-acceptance claims. A generator-only or producer-only future path is
implementation/parity history, not latent verifier evidence. Mere missing
integration evidence remains a dependency or lead.

## Deliverable

Report each selected invariant independently with its complete necessary
participant set, confirmed findings, leads, closures, artifacts, and explicit
exclusions. For a bounded surface or domain-wide review, include the coverage
ledger and do not stop after the first invariant. Never imply that reviewing
memory or timestamp covered delegation, setup authorization, lookup
aggregation, padding, recursion, or settlement unless each was separately
reviewed.

Keep the work authorized, source-local, read-only, and defensive. Do not build
malicious provers or operational proof forgeries.
