# Verifier-Review Suite Design Requirements

Preserve these when revising the coordinator or any specialist.

## Suite architecture

- Treat `zk-verifier-review` plus its named specialists as one installable
  suite. Keep canonical shared references in the coordinator and let specialists
  link directly to them instead of copying large theory files into every skill.
  If distributing a specialist, distribute the suite or vendor the referenced
  files; do not silently leave broken sibling links.
- Keep each specialist's procedural contract self-contained enough to preserve
  target scoping, safety, local transcript obligations, evidence standards, and
  deliverables without loading coordinator methodology prose.
- Keep specialist trigger descriptions narrow and mutually intelligible. A
  generic whole-system or routing request should select the coordinator; a
  named domain/component should select the matching specialist rather than all
  skills simultaneously.
- Route non-matching targets away from the repository profile. A bundled
  profile is not automatically applicable; it must pass its own applicability
  check first.
- Support both sumcheck/GKR-based and AIR/STARK-based verifiers, and the
  migration state where a repository contains traces of both.
- Support native/recursive verifiers and final Solidity/Yul or equivalent
  on-chain settlement verifiers without assuming they share a field, hash, or
  proof encoding.

## Scope discipline

- Bound a specialist run by one concrete entrypoint/component, one proof-system
  instance/configuration, and one phase, invariant, or statement boundary. A
  complete audit is a matrix of bounded runs, not one agent context.
- Require one coordinator-built verifier model before a multi-run campaign:
  accepted statement, round table, prover-freedom ledger, claim/handoff graph,
  implementation-layer map, and configuration matrix. Specialists consume and
  correct bounded slices instead of rebuilding incompatible global models.
- For composition, permit the selected invariant to span all necessary circuit
  families/proof classes, but do not let that broaden into unrelated global
  arguments. Treat composition as the horizontal join across participating
  cells, not as a file-local peer review.
- Make local transcript reconstruction mandatory inside every challenge-
  dependent specialist. The transcript specialist owns the complete selected
  schedule; protocol, composition, soundness, and recursion specialists own and
  emit the rows necessary for their target. Reconcile overlaps instead of
  assuming a prior transcript pass made protocol ordering correct.
- Classify implementation relationships before parity work. Do not demand the
  same proof language from independent outer instances that deliberately use a
  different field, hash, encoding, or commitment scheme.
- Default to the verifier, where the acceptance predicate converges. Permit an
  explicitly requested prover-first review, but label its verification contract
  provisional and schedule verifier-side confirmation. Use the prover as
  evidence of message format and the papers as evidence of soundness
  obligations, never the reverse.

## Method

- Enumerate **prover freedoms**, not verifier checks. Both ledgers — the round
  table and the freedom ledger — must remain first-class deliverables.
- Require specification recovery before judgement. Deliberate deviations must
  be recorded together with the claimed reason they are sound; that claim is
  the audit target.
- Establish the concrete field and encoding API before applying canonicity or
  raw-representation heuristics.
- Keep the "every prover-supplied value is adversarial until constrained"
  principle stated as a first principle, not buried in a checklist.
- Keep the verifier-specific gate traps explicit: `debug_assert!` is not a
  check; a check the honest prover satisfies is not necessarily a binding; a
  recomputation whose comparison is dropped is not a check; an empty-container
  early return is a vacuous success.
- Treat syntactically present but semantically degenerate checks as a standing
  cross-cutting class: zero coefficients, hardcoded challenges, inactive
  selectors, empty generator arms, discarded authenticated outputs, zero-valued
  security parameters, and checks gated to only one participant or default
  configuration.
- For generated verifiers, require reading the emitted code, not only the
  generator.
- Overlay implementation-layer coverage on every protocol cell: handwritten
  verifier, generator, emitted artifact, producer/serializer, recursive mirror,
  caller, and settlement boundary. Domain coverage does not imply artifact-layer
  coverage.
- For on-chain verifiers, require tracing generated source through exact
  compiler settings and deployed runtime bytecode to the state-transition
  caller; transaction success, an event, or an unauthenticated registry mark is
  not by itself proof acceptance.
- Require checking every security level, feature gate, and target `cfg` that
  selects a verification path, and require saying which were checked.
- Require provenance and reproducible regeneration for trusted setup caps,
  verifier keys, imported constants, program identities, and deployment
  parameters.
- Require each specialist to emit a compatible target fingerprint, claim or
  boundary handoff, local transcript/proof-data rows, candidate disposition,
  coverage limits, and dependent next cells so the coordinator can integrate
  without laundering assumptions.
- Keep quantitative security accounting separate from local protocol
  correctness. Protocol specialists emit concrete local error terms and
  hypotheses; the soundness specialist independently validates and composes
  them under one stated experiment and retry/work model.

## Evidence and honesty

- Prefer precision over volume. A confirmed finding needs a traced accepting
  run on a false statement with every applicable check enumerated, or, for
  completeness, a rejected honest proof.
- Keep unresolved concerns, parameter questions, and specification conflicts
  outside the confirmed findings, and never drop them.
- Never claim independent or cross-model validation unless it occurred; never
  claim implementation parity was verified when only a parity document was
  read.
- Keep an honest coverage ledger, including which phases and which
  configurations were not traced.
- For a campaign, maintain a matrix whose rows are concrete verifier convergence
  points and whose columns are applicable specialist focuses. Never infer one
  cell from a neighboring circuit family, security level, proof-system instance,
  generated artifact, or implementation language.
- Preserve a verified-closures ledger so recurring false positives are closed
  with exact evidence and revalidated after version changes.

## Safety

- Keep the review read-only and defensive. No forged-proof generators, no
  malicious-prover harnesses, no operational reproduction, no live-system
  targeting. Propagate the boundary verbatim to delegated prompts.
- Remediation is stated as the missing binding plus the regression property a
  negative test must assert.

## Maintenance

- Keep repository-specific content in a versioned, fingerprinted profile with
  an applicability check, a file map, the reconstructed round schedule, and an
  explicit list of the mechanics most likely to rot.
- Keep profiles as maps, invariants, revalidation prompts, and verified
  closures—not as a backlog of findings. If inspection discovers a
  findings-shaped fact (for example an unauthenticated entrypoint, discarded
  call result, or explicit missing-check TODO), record it in a dated audit
  artifact with the exact commit/configuration and evidence gate. Rewrite the
  profile entry as a neutral instruction to re-derive the property from source.
- Do not let source observations become inherited truth. A later reviewer must
  independently re-check profile hazards and must not cite the profile itself
  as evidence that a vulnerability exists or was fixed.
- Re-verify each profile hazard against the checkout before relying on it, and
  record the delta rather than editing the profile in place during a review.
- Cite exact primary sources for paper-derived constructions. Separate the
  stable protocol obligation from a version-specific implementation of it.
- Keep one canonical reference per topic. Merge overlapping compact/expanded
  pairs instead of resolving duplication only through precedence. Keep
  reference loading progressive by review pass instead of requiring every
  large reference before source inspection.
- Large subsystem references are justified only when that subsystem is in the
  selected scope. In particular, do not load the Solidity/Yul/L1 chapter for a
  Rust-only focused review; retain its depth for audits whose final acceptance
  boundary is on-chain.
- Keep the soundness reference explicit about theorem versions, proximity-gap
  hypotheses, actual challenge support, probability composition, and retry
  work. Do not encode the heuristic “PoW simply adds bits” as a general rule.
- Avoid personal names, private conversation details, and organization-internal
  rationale not needed to execute the review.
- Add only independently verified historical examples, and keep any blind
  evaluation answers outside the installed skill.
