---
name: zk-circuit-review
description: Defensively review one named AIR, PLONK-style, or GKR algebraic circuit, or an explicitly requested small group of closely related circuits, for constraint-soundness and material completeness failures. Use for authorized, read-only ZKP circuit audits and correctness reviews, including when the user has not yet supplied the circuit name or path.
---

# Defensive ZK Circuit Review

Audit one user-supplied circuit target by default. Accept a small group only when the user explicitly requests the circuits together. Default to a deep, read-only defensive review. Return a high-precision relation-correctness report, not a general code review.

## Defensive objective

Establish whether the enforced algebraic relation matches the circuit's intended relation.

- Treat witness generation as an implementation of the honest case, never as a constraint guarantee.
- Treat a **soundness bug** as an invalid statement, witness, operation, or transition that satisfies every applicable constraint under the stated assumptions.
- Treat a **material completeness bug** as a valid intended case that cannot satisfy the circuit or cannot be represented. Do not confuse this with redundant constraints or inefficiency.
- Exclude style, performance, maintainability, ordinary Rust safety, panic, and denial-of-service observations from soundness findings unless they change the accepted relation.

## Safety and authorization boundary

Treat the task as authorized defensive source review whose outcomes are
identification, prevention, and remediation of local constraint defects. Keep
all analysis inside the supplied repository snapshot and normative public
specifications.

- Do not generate or execute proof-generation exploits, attack scripts,
  deployment-specific payloads, network probes, credential or access steps, or
  procedures for targeting a live system.
- Do not provide an operational reproduction recipe. Establish a soundness
  finding with source-local algebraic evidence: a bounded symbolic assignment
  or finite abstract trace that fixes every relevant selector, tuple field, and
  witness degree of freedom and shows why every applicable relation is
  satisfied while the intended relation is violated.
- Do not include concrete secrets, real user data, production endpoints, or
  instructions for abusing a deployed prover or verifier.
- Keep remediation defensive: state the missing invariant and the regression
  property to test. Implementation guidance may describe constraints and tests,
  but not an offensive workflow.

Read [algebraic-circuit-model.md](references/algebraic-circuit-model.md) and [review-methodology.md](references/review-methodology.md) before analyzing the target.

## Require a target

Identify circuit targets only from the user's request. A target may be a circuit name, symbol, module, file path, or other identifier that can be resolved to an exact constraint entrypoint.

- If the user supplied no circuit target, do not choose one from the repository and do not begin a broad audit. Ask: **“Which circuit should I audit? One circuit is recommended; you may name a small group only if they are tightly related and should be reviewed together, such as word and subword memory circuits.”** Wait for the answer.
- If the user supplied one target, audit that target.
- If the user explicitly supplied several targets, audit them together. Do not silently expand a single target to neighboring circuits or an entire family.
- If wording such as “the memory circuits” could resolve to several targets but does not clearly request all of them, list the likely exact targets briefly and ask the user to choose one or explicitly approve the group.

One circuit is preferred because it permits deeper constraint tracing and more reliable validation. A grouped review is appropriate when the targets implement tightly coupled variants, share substantial machinery, or must be compared to establish their intended relation. Do not reject an explicit multi-circuit request merely because one is preferred.

## Resolve and bound each target

Resolve every supplied target to one exact circuit entrypoint before judging constraints. Use repository evidence to resolve aliases and paths. If a supplied name matches multiple materially different entrypoints, ask the user when choosing among them would change the reviewed statement and the request does not clearly include all of them.

After resolving the entrypoint, enumerate every semantically matching internal
implementation, generated variant, fixed table, and profile-selected path that
can contribute to that statement. Do not silently choose the first name match.
Exclude a candidate implementation as historical, unused, or unreachable only
after a repository-wide call-site and configuration search establishes that
status; record the evidence so later discoveries can overturn the exclusion.

Build a scope manifest for each target containing:

- the resolved circuit and intended statement;
- constraint construction and generated/lowered constraint files;
- witness-generation files, used only to recover intent and constraint surfaces;
- layouts, columns, gates, tables, selectors, challenges, and configurations;
- call sites, proving profiles, tests, and specification or architecture documents;
- local verifier or completion logic needed to enforce outputs of this circuit;
- public inputs, outputs, and commitments;
- assumed global, inter-circuit, and inter-chunk invariants.

For a grouped review, also identify shared code, shared tables/arguments, cross-target assumptions, and semantic differences. Maintain target-specific coverage and evidence: a constraint found in one circuit does not close a gap in another unless enforced through a verified shared or cross-circuit relation.

Do not assume any repository path, language, ISA, or circuit framework from the skill itself. Select repository-specific references only after identifying the target architecture:

- For any RISC-V circuit, read [riscv32-machine-baseline.md](references/riscv32-machine-baseline.md).
- For the fingerprinted Airbender V3 GKR repository state, run the applicability check in [airbender-v3-machine-profile.md](references/airbender-v3-machine-profile.md), then read [airbender-v3-circuit-architecture.md](references/airbender-v3-circuit-architecture.md).
- For another Airbender version, use the nearest profile only as a hypothesis/search checklist and recover a version delta from the active proving entrypoint before confirming findings.
- For Boojum, a non-RISC-V target, or an unrelated repository, do not load the Airbender or RV32 references merely because they are bundled with this portable skill.

## Recover the specification before auditing

Do not reconstruct the intended relation from constraint code alone. Before evaluating constraints, build a compact specification dossier containing:

- the normative baseline or external standard;
- the selected versioned project profile, its repository/commit fingerprint, applicability result, and observed delta;
- the exact target circuit and active proving/decoder profile;
- explicitly intended project deviations and custom operations;
- supported, unsupported, trapped, preprocessed, and profile-disabled cases;
- instruction/operation semantics, exceptional cases, state changes, and external argument effects;
- unresolved conflicts between documentation, configuration, simulator, tests, and circuit code.

Use implementation code to determine what is enforced, not silently to redefine what should be enforced. Treat witness generators, simulators, and tests as corroborating evidence unless the repository explicitly designates them as specification. If authoritative sources conflict, record a specification question and avoid confirming a finding until the intended rule is resolved.

For a matching Airbender V3 target, begin with the normative RV32 baseline and fingerprinted project profile. Validate the bounded fingerprint/delta checklist, then trace only changed or target-relevant semantics through the selected decoder configuration, fixed-bytecode preprocessing, opcode-family decoder, target circuit, simulator/replayer, and verifier-visible machine state. Do not spend the audit rediscovering standard RV32I semantics from Rust. If the profile does not match, do not silently inherit its deviations.

## Scope and assumptions

Unless the user requests a proof-system audit, assume that the field implementation, polynomial commitment scheme, Sumcheck/GKR/FRI/PCS machinery, and verifier correctly enforce every declared claim according to their documented interfaces.

Also assume explicitly identified global arguments are sound as global mechanisms. Typical assumptions include whole-system RAM/permutation consistency, cross-circuit buses, recursive composition, and continuity across proving chunks.

Do not use these assumptions to skip the circuit's local obligations. Verify that this circuit:

- constrains every field of each emitted or consumed tuple;
- derives participation selectors and multiplicities correctly;
- uses the intended encoding and ordering;
- binds local state and outputs to the argument contribution;
- initializes, updates, exposes, or completes local accumulators as required;
- cannot create a malformed contribution that remains valid even if the global argument is otherwise consistent.

An assumption bounds what you audit for defects. It never bounds what you may
read. Assuming a dependency is correct is what obliges this circuit to match the
contract that dependency actually implements, so when a candidate turns on what
a dependency really does, go read it and answer the question. Follow it into the
field/backend, tables, decoder, generated code, simulator, or callers until the
snapshot settles it. Only record a concern as unresolved after confirming the
answer is genuinely absent from the snapshot rather than merely unread. A hard
circuit is one whose correctness depends on context outside its own file; search
harder before demoting a candidate.

Record every assumed global invariant and the locally checked interface in the report. Treat an unreviewed global invariant as a coverage dependency, not a vulnerability. Read [global-arguments-scope.md](references/global-arguments-scope.md).

## Review workflow

1. Complete the specification dossier above. For every operation in the target, record operands, result, next state, memory/register effects, activation/profile rules, traps, and project deviations. Mark uncertain claims as provisional.
2. Build a variable map and a semantic-constraint coverage ledger. Trace each critical value from origin through transformations, local constraints, aggregation, argument outputs, and public statement.
3. Enumerate all intended cases and activation domains: operation variants, selector combinations, real/padding rows, first/last rows, exceptional field values, and chunk boundaries.
4. Run independent discovery passes over:
   - specification, case completeness, and public statement binding;
   - witnesses, equalities, arithmetic relations, ranges, and state/data flow;
   - selectors, transitions, boundaries, padding, exceptional values, and preprocessing;
   - lookups/LogUp, challenges, degree, GKR wiring, aggregation, and local/global interfaces.
   Weight these passes across defect classes, not toward whichever class is
   easiest to enumerate. Missing bounds are only one family: a relation can also
   carry the wrong sign, the wrong constant, the wrong operand, the wrong table,
   a wrong bit position or limb order, or omit a branch from a shared aggregate.
   An equation whose every term is range-checked can still enforce the wrong
   relation. When a pass reports only range-check concerns, treat that as a
   signal the other classes were not searched.
   Compare intended semantics with the relation actually enforced for every
   supported operation form. Follow values across representation changes and
   shared helpers instead of assuming that locally plausible pieces compose to
   the intended result.
   Maintain a relation worksheet for each operation form with the intended
   expression, honest witness/reference expression, exact enforced expression,
   and activation condition. Compare lookup and argument fields after selector
   choice and packing. Normalize multi-limb arithmetic into one radix identity
   and compare every operand, constant, operation-specific term, carry, and borrow
   coefficient separately for initial, recurrent, and final limbs. At each
   representation boundary, record the source encoding, destination encoding,
   and conversion equation. A later relation closes a discrepancy only when it
   binds the same expressions on the same activation domain.
   Finding one defect does not clear neighboring operations or shared branches;
   finish each worksheet or mark it explicitly unreviewed.
5. For every candidate, search for direct and indirect constraints that may close the gap. Construct the smallest complete bounded symbolic invalid assignment or finite abstract trace, enumerate every applicable relation and global-interface condition, and show why each is satisfied while the intended relation is violated. For completeness, provide a concrete valid rejected case. Never turn this evidence into executable proof-generation or operational attack instructions.
6. Maintain the candidate disposition ledger defined in
   [review-methodology.md](references/review-methodology.md). Before finalizing,
   reconcile scope decisions, closed leads, and coverage claims with everything
   learned later in the review. Reopen a conclusion when call sites,
   configuration, or relation evidence contradicts it.
7. Apply the evidence gate below. Discard or demote every candidate that fails it.
8. Return the report in [finding-format.md](references/finding-format.md).

Continue until the coverage ledger is complete or remaining areas are explicitly listed as unreviewed. Finding nothing is acceptable; never lower the evidence threshold to fill the report.

## Independent validation

When the host supports delegation, run up to four discovery roles independently. Then give each candidate to a fresh skeptical validator using the relevant source, intended invariant, observed equations, and proposed symbolic mismatch. Ask the validator to search for overlooked constraints and disprove the claimed relation gap rather than endorse the candidate.

Propagate the safety and authorization boundary to every delegated prompt. A
discovery or validation role must remain source-local and defensive and must not
be asked for executable proof generation, an operational reproduction, or
live-system targeting.

Use a second validation round only when the first validator identifies a specific unresolved dependency. Prefer a different model or provider when the host exposes one, but never claim cross-model validation unless it actually occurred.

When delegation is unavailable, perform the same role-separated passes sequentially and re-read source evidence before validation. Do not claim independent-agent validation in that case.

## Evidence gate for main findings

Include a candidate under confirmed findings only when all conditions hold:

1. Establish the intended invariant from repository evidence and cite it.
2. Enumerate all applicable direct and indirect constraints, lookups, wiring, and activation conditions.
3. Show a complete bounded symbolic invalid assignment or finite abstract trace, or a valid rejected case. Fix every relevant selector, tuple field, and witness degree of freedom; enumerate the applicable direct and indirect relations; and show why each relation is satisfied. Include only evidence needed to prove the mismatch, and do not provide executable exploit or live-system reproduction steps.
4. Check reachability under selectors, preprocessing, table setup, padding, boundaries, and stated global assumptions.
5. Trace the impact to the proved statement, state transition, output, or supported operation set.
6. Survive a skeptical verification pass with no unidentified constraint that could invalidate the claim.

If any condition is missing, place the item under unverified leads or scope dependencies, not confirmed findings.

## Reference routing

Always read:

- [algebraic-circuit-model.md](references/algebraic-circuit-model.md)
- [review-methodology.md](references/review-methodology.md)
- [global-arguments-scope.md](references/global-arguments-scope.md)
- [finding-format.md](references/finding-format.md)

Read the applicable specialist references:

- witness coverage: [underconstraints.md](references/underconstraints.md), [equality-and-copy-constraints.md](references/equality-and-copy-constraints.md)
- domains and exceptional values: [range-and-booleanity.md](references/range-and-booleanity.md), [inverses-and-exceptional-values.md](references/inverses-and-exceptional-values.md)
- activation and trace shape: [selectors-and-gating.md](references/selectors-and-gating.md), [transitions-and-boundaries.md](references/transitions-and-boundaries.md), [padding.md](references/padding.md)
- operations and fixed data: [opcode-and-decoding.md](references/opcode-and-decoding.md), [preprocessing-and-fixed-tables.md](references/preprocessing-and-fixed-tables.md)
- external statement: [public-io-binding.md](references/public-io-binding.md)
- algebraic arguments: [lookups-and-logup.md](references/lookups-and-logup.md), [memory-and-ram.md](references/memory-and-ram.md), [fiat-shamir.md](references/fiat-shamir.md), [degree-bounds.md](references/degree-bounds.md)
- GKR or layered circuits: [gkr-wiring-and-aggregation.md](references/gkr-wiring-and-aggregation.md)
- RISC-V circuits: [riscv32-machine-baseline.md](references/riscv32-machine-baseline.md)
- matching Airbender V3 GKR circuits only: [airbender-v3-machine-profile.md](references/airbender-v3-machine-profile.md), [airbender-v3-circuit-architecture.md](references/airbender-v3-circuit-architecture.md)

When maintaining this skill, preserve the requirements in [design-requirements.md](references/design-requirements.md).
