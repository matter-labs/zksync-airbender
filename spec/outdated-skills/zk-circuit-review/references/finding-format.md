# Report Format

Use concise language and exact source locations. Do not call an unresolved concern a finding.

## 1. Executive summary

State the target or explicitly requested target group, overall result, number of confirmed soundness findings, number of confirmed material completeness failures, and important coverage limits.

## 2. Scope and assumption ledger

List:

- each resolved circuit and its reviewed implementation layers;
- intended statement and specification sources, including the selected project-profile ID, repository/commit fingerprint, applicability result, and any current-version delta;
- proof-system properties assumed correct;
- global, inter-circuit, and inter-chunk invariants assumed correct;
- local interfaces checked under each assumption;
- components not reviewed.

## 3. Confirmed soundness findings

Include only soundness failures that pass every evidence gate.

```text
## [SEVERITY] Title

Location:
Exact files, functions, gates, constraints, and relevant lines.

Target invariant:
The exact relation that must hold and its specification evidence.

Observed enforcement:
All applicable equations, lookups, wiring, selectors, and assumptions.

Symbolic relation mismatch:
The minimum complete bounded symbolic invalid assignment or finite abstract
trace that satisfies the observed enforcement. Fix every relevant selector,
tuple field, and witness degree of freedom, then show why every applicable
direct and indirect relation is satisfied. Do not include executable
proof-generation code, operational reproduction steps, or live-system targeting
instructions.

Reachability and impact:
Why the symbolic mismatch is admitted and how it changes the proved statement.

Validation performed:
Indirect constraints searched, assumptions checked, and independent/sequential validation actually performed.

Recommended missing invariant and regression property:
Describe the required defensive relation and the property a local regression
test must assert, without providing an offensive workflow.
```

Use severity according to effect on the accepted computation, not code quality.

For a grouped review, identify the affected target or targets in every finding. Do not imply that a finding applies to a sibling circuit without independently tracing the relevant enforcement there.

## 4. Confirmed material completeness failures

Use the same structure, replacing the counterexample with a concrete valid intended case that the circuit rejects or cannot represent. Exclude mere redundancy and performance loss.

## 5. Unverified leads and specification questions

List plausible concerns that did not pass the evidence gate. State exactly what evidence is missing and where you searched for it. Before filing here, confirm the missing evidence is genuinely absent from the snapshot rather than merely unread; if the snapshot answers it, resolve the concern and place the result in section 3 or 4 instead.

Never drop a concern for being unresolved. Where the circuit demonstrably disagrees with the reference implementation or another in-repo contract but you cannot establish which side is normative, record it here as an uncertain, specification-undefined finding: state both relations, their exact difference, the affected operations, and the evidence that would settle it. Keep these separate from confirmed findings and assign no security severity.

## 6. Global and system-level dependencies

For each unreviewed global, inter-circuit, or inter-chunk invariant, state:

- the assumed invariant;
- this circuit's local contribution;
- what local interface was checked;
- what remains for a later system audit.

Do not repeat a standard, correctly wired dependency as a vulnerability.

## 7. Unimportant observations

Optionally list concise non-security observations such as inefficiency, redundant constraints, maintainability, or implementation quality. Keep this section last and clearly label it non-security.

## 8. Coverage and candidate-disposition appendix

Summarize the semantic coverage ledger and relation worksheets, and identify any
incomplete review area. Include a concise report view of the canonical candidate
disposition ledger defined in [review-methodology.md](review-methodology.md),
covering each material lead and its exact closure or remaining gap. This is an
auditability record, not a place to inflate findings. If no confirmed issue
exists, say `No confirmed findings` without inventing lower-confidence findings.
