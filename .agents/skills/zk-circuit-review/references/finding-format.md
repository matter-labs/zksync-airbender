# Report Format

Use concise language and exact source locations. Do not call an unresolved concern a finding.

## 1. Executive summary

State the target or explicitly requested target group, overall result, number of confirmed security findings, number of confirmed material completeness failures, and important coverage limits.

## 2. Scope and assumption ledger

List:

- each resolved circuit and its reviewed implementation layers;
- intended statement and specification sources, including the selected project-profile ID, repository/commit fingerprint, applicability result, and any current-version delta;
- proof-system properties assumed correct;
- global, inter-circuit, and inter-chunk invariants assumed correct;
- local interfaces checked under each assumption;
- components not reviewed.

## 3. Confirmed security findings

Include only soundness failures that pass every evidence gate.

```text
## [SEVERITY] Title

Location:
Exact files, functions, gates, constraints, and relevant lines.

Target invariant:
The exact relation that must hold and its specification evidence.

Observed enforcement:
All applicable equations, lookups, wiring, selectors, and assumptions.

Counterexample:
A concrete invalid assignment or trace satisfying the observed enforcement.

Reachability and impact:
Why the counterexample is reachable and how it changes the proved statement.

Validation performed:
Indirect constraints searched, assumptions checked, and independent/sequential validation actually performed.

Recommended missing invariant:
Describe the required relation without prescribing an implementation unless useful.
```

Use severity according to effect on the accepted computation, not code quality.

For a grouped review, identify the affected target or targets in every finding. Do not imply that a finding applies to a sibling circuit without independently tracing the relevant enforcement there.

## 4. Confirmed material completeness failures

Use the same structure, replacing the counterexample with a concrete valid intended case that the circuit rejects or cannot represent. Exclude mere redundancy and performance loss.

## 5. Unverified leads and specification questions

List plausible concerns that did not pass the evidence gate. State exactly what evidence is missing. Keep these separate from findings and assign no security severity.

## 6. Global and system-level dependencies

For each unreviewed global, inter-circuit, or inter-chunk invariant, state:

- the assumed invariant;
- this circuit's local contribution;
- what local interface was checked;
- what remains for a later system audit.

Do not repeat a standard, correctly wired dependency as a vulnerability.

## 7. Unimportant observations

Optionally list concise non-security observations such as inefficiency, redundant constraints, maintainability, or implementation quality. Keep this section last and clearly label it non-security.

## 8. Coverage appendix

Summarize the semantic coverage ledger and identify any incomplete review area. If no confirmed issue exists, say `No confirmed findings` without inventing lower-confidence findings.
