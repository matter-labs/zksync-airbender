---
name: living-spec
description: Interactively create and evolve the modular proof-system living specification under spec/ from project decisions, standards, implementation evidence, and explicit gaps. Use when asked to add, revise, reconcile, or discuss specification modules; do not use for ordinary audits or implementation work.
---

# Living Specification

Help a human evolve the proof-system specification one bounded slice at a time. The
current `spec/` tree is the baseline; the skill is a maintenance workflow, not a
substitute for project decisions.

Before every specification edit, read [STYLE.md](STYLE.md). It is the primary guide
for how the document should read and look. Read
[specification-format.md](references/specification-format.md) when adding or
restructuring statement IDs, modules, or shared notation. Read `spec/METADATA.md`
when adding or reconciling statement metadata.

Read [reconciliation.md](references/reconciliation.md) when the implementation or
profile revision changed, an anchor disappeared, an executable check failed, or the
user asks whether an existing module still matches its evidence.

## Interactive working mode

1. Read `spec/INDEX.md`, the requested module, and its direct dependencies.
2. Bound one semantic component or one cross-component invariant. Do not attempt to
   complete the whole proof system unless explicitly requested.
3. Recover candidate semantics from adopted standards, explicit project decisions,
   history, and the active implementation path.
4. Follow `STYLE.md`: partition materially branching behavior into a shallow decision
   tree ordered from the outer activation/mode gate inward. Treat assumptions as tree
   context, keep stable IDs beside canonical statements, and consolidate provenance
   in the final metadata table.
5. Preserve uncertainty. Mark a claim `provisional` when its evidence is limited to
   implementation detail, is conflicting, or leaves intendedness genuinely unclear.
   A relation aligned with an adopted standard, explicit human direction, or
   convergent constraint, architecture, test, and human evidence may be normative for
   its stated profile. Every provisional claim or tightly related provisional group
   must map to a narrow `GAP` stating what evidence, review, or decision would permit
   promotion.
6. Surface human decisions that would materially change the accepted relation. Apply
   confirmed decisions and continue with unaffected statements without blocking.
7. Update `spec/INDEX.md` only when module scope, status, dependencies, or global gaps
   change.
8. Validate IDs, metadata coverage, activation, dependency/discharge edges, links,
   domains, decision-tree branch coverage, and typed source locators.
9. When a confirmed defect informs the edit, identify the exact statement violated by
   the defective implementation and tag its bug class. Distinguish semantic coverage
   from shape-only detection; do not claim coverage from topical similarity.

Prefer proposing or editing a small coherent set of statements that the human can
review. Preserve human rewrites unless they create a contradiction or ambiguity; then
identify the exact conflict.

Never rewrite a claim merely to match changed code. Reconciliation must classify the
change as locator-only, intended semantic change, implementation mismatch, or unresolved
intent. Missing enforcement and failed checks require explicit treatment; they are not
ordinary source-locator maintenance.

## Evidence discipline

- `normative`: explicit project decision, adopted external standard with project
  deviations applied, or a strongly corroborated relation adopted for the stated
  profile from independent constraint, architecture, test, and human evidence.
- `provisional`: a candidate relation supported only by implementation detail, or one
  whose evidence or intendedness remains materially incomplete or conflicting.
- `open`: `GAP` only; one missing decision, conflict, or evidence boundary.

Constraints and verifier checks show what is enforced, not necessarily what was
intended. Decoder, witness, simulator, and tests show honest behavior, not independent
enforcement. Trace important statements from inputs/configuration through constraints
or verification to the exported claim.

Record the inspected revision, dirty-worktree state, active profile, and stable source
symbols. A single matching code path is not enough for promotion; use the adopted
standard, human direction, or convergent independent evidence that establishes the
relation.

## Modular reasoning

- One module owns one semantic relation and its interface.
- Import another module's guarantee through `ASM`; export through `OUT`.
- Keep each module understandable after replacing its assumptions with axioms.
- Split modules when they have distinct proof contexts or can be reviewed under
  explicit assumptions.

For Airbender machine/circuit work, consult only the relevant sibling references:

- [RISC-V baseline](../zk-circuit-review/references/riscv32-machine-baseline.md)
- [machine history/profile](../zk-circuit-review/references/airbender-v3-machine-profile.md)
- [circuit architecture](../zk-circuit-review/references/airbender-v3-circuit-architecture.md)
- [GKR wiring](../zk-circuit-review/references/gkr-wiring-and-aggregation.md)
- [global arguments](../zk-circuit-review/references/global-arguments-scope.md)

Treat these as versioned priors and reconcile them with current entrypoints.

## Ethproofs W2

When the requested change affects W2 coverage, read `spec/ETHPROOFS-W2.md`. Keep the
external deliverable checklist separate from Airbender's normative accepted relation.
Update the coverage table or gaps only when the specification gains or loses material
coverage.

## Handoff

Report changed modules, covered revision/profile, per-ID reconciliation outcomes,
provisional IDs, open gaps and the exact human decisions they need, plus implementation
mismatches in a separate section. Do not turn the specification itself into an audit
report or propose committing agent-only artifacts.
