---
name: zk-circuit-review
description: Deeply audit one named AIR, PLONK-style, or GKR algebraic circuit, or an explicitly requested small group of closely related circuits, for exploitable underconstraints and material completeness failures. Use when asked to audit, review, or security-check ZKP circuits, including when the user has not yet supplied the circuit name or path.
---

# ZK Circuit Security Review

Audit one user-supplied circuit target by default. Accept a small group only when the user explicitly requests the circuits together. Default to a deep, read-only review. Return a high-precision security report, not a general code review.

## Security objective

Establish whether the enforced algebraic relation matches the circuit's intended relation.

- Treat witness generation as an implementation of the honest case, never as a security guarantee.
- Treat a **soundness bug** as an invalid statement, witness, operation, or transition that satisfies every applicable constraint under the stated assumptions.
- Treat a **material completeness bug** as a valid intended case that cannot satisfy the circuit or cannot be represented. Do not confuse this with redundant constraints or inefficiency.
- Exclude style, performance, maintainability, ordinary Rust safety, panic, and denial-of-service observations from security findings unless they change the accepted relation.

Read [algebraic-circuit-model.md](references/algebraic-circuit-model.md) and [review-methodology.md](references/review-methodology.md) before analyzing the target.

## Require a target

Identify circuit targets only from the user's request. A target may be a circuit name, symbol, module, file path, or other identifier that can be resolved to an exact constraint entrypoint.

- If the user supplied no circuit target, do not choose one from the repository and do not begin a broad audit. Ask: **“Which circuit should I audit? One circuit is recommended; you may name a small group only if they are tightly related and should be reviewed together, such as word and subword memory circuits.”** Wait for the answer.
- If the user supplied one target, audit that target.
- If the user explicitly supplied several targets, audit them together. Do not silently expand a single target to neighboring circuits or an entire family.
- If wording such as “the memory circuits” could resolve to several targets but does not clearly request all of them, list the likely exact targets briefly and ask the user to choose one or explicitly approve the group.

One circuit is preferred because it permits deeper constraint tracing and more reliable validation. A grouped review is appropriate when the targets implement tightly coupled variants, share substantial machinery, or must be compared to establish their intended relation. Do not reject an explicit multi-circuit request merely because one is preferred.

## Resolve and bound each target

Resolve every supplied target to one exact circuit entrypoint before judging constraints. Use repository evidence to resolve aliases and paths. If a supplied name matches multiple materially different entrypoints, ask the user when choosing among them would change the security statement and the request does not clearly include all of them.

Build a scope manifest for each target containing:

- the resolved circuit and intended statement;
- constraint construction and generated/lowered constraint files;
- witness-generation files, used only to recover intent and attack surfaces;
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
5. For every candidate, search for direct and indirect constraints that may close the gap. Construct a concrete malicious satisfying assignment or a concrete valid rejected case.
6. Apply the evidence gate below. Discard or demote every candidate that fails it.
7. Return the report in [finding-format.md](references/finding-format.md).

Continue until the coverage ledger is complete or remaining areas are explicitly listed as unreviewed. Finding nothing is acceptable; never lower the evidence threshold to fill the report.

## Independent validation

When the host supports delegation, run up to four discovery roles independently. Then give each candidate to a fresh skeptical validator using the relevant source, intended invariant, observed equations, and proposed counterexample. Ask the validator to search for overlooked constraints and disprove exploitability rather than endorse the candidate.

Use a second validation round only when the first validator identifies a specific unresolved dependency. Prefer a different model or provider when the host exposes one, but never claim cross-model validation unless it actually occurred.

When delegation is unavailable, perform the same role-separated passes sequentially and re-read source evidence before validation. Do not claim independent-agent validation in that case.

## Evidence gate for main findings

Include a candidate under confirmed findings only when all conditions hold:

1. Establish the intended invariant from repository evidence and cite it.
2. Enumerate all applicable direct and indirect constraints, lookups, wiring, and activation conditions.
3. Show an explicit invalid satisfying assignment/trace or valid rejected case; use symbolic values only when they are sufficient to prove the claim.
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
