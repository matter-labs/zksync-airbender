# Skill Design Requirements

Preserve these when revising the skill.

## Portability

- Keep the skill vendor-neutral and usable from a copied standalone folder. Do
  not depend on a sibling skill's files, a shared reference directory, or any
  host-specific path. Cross-skill pointers must be optional enrichment.
- Route non-matching targets away from the repository profile. A bundled
  profile is not automatically applicable; it must pass its own applicability
  check first.
- Support both sumcheck/GKR-based and AIR/STARK-based verifiers, and the
  migration state where a repository contains traces of both.
- Support native/recursive verifiers and final Solidity/Yul or equivalent
  on-chain settlement verifiers without assuming they share a field, hash, or
  proof encoding.

## Scope discipline

- Fix one verifier and one review mode before analyzing. Do not silently expand
  a named component into a whole-system audit, and do not silently narrow a
  whole-verifier request to one function.
- Keep the transcript pass first and mandatory when any other protocol pass
  runs; the round table is its output and the other passes consume it.
- Classify implementation relationships before parity work. Do not demand the
  same proof language from independent outer instances that deliberately use a
  different field, hash, encoding, or commitment scheme.
- Audit the verifier. Use the prover as evidence of message format and the
  papers as evidence of soundness obligations, never the reverse.

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
- For generated verifiers, require reading the emitted code, not only the
  generator.
- For on-chain verifiers, require tracing generated source through exact
  compiler settings and deployed runtime bytecode to the state-transition
  caller; transaction success, an event, or an unauthenticated registry mark is
  not by itself proof acceptance.
- Require checking every security level, feature gate, and target `cfg` that
  selects a verification path, and require saying which were checked.
- Require provenance and reproducible regeneration for trusted setup caps,
  verifier keys, imported constants, program identities, and deployment
  parameters.

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
- Avoid personal names, private conversation details, and organization-internal
  rationale not needed to execute the review.
- Add only independently verified historical examples, and keep any blind
  evaluation answers outside the installed skill.
