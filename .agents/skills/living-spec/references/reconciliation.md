# Living Specification Reconciliation

Use this procedure to decide whether an existing specification statement remains
supported after its implementation, profile, authority source, anchor, or check changes.
The objective is semantic reconciliation, not making metadata look current.

## Establish the comparison

For the bounded module or statement set:

1. Read each existing claim, activation, authority, dependencies, source, and anchor.
2. Identify the prior evidence revision and the current implementation/profile.
3. Read the current enforcing constraint or verifier check. Use witness generation,
   decoder tables, simulators, tests, and history only as corroborating intent evidence.
4. If an `OUT` or interface statement may change, identify its direct consumers from
   `spec/INDEX.md` and inspect their importing `ASM` statements.

Compare relations in semantic terms: admitted domain, activation, equation, rejection
condition, preserved state, and exported value. A changed file or hash alone is not a
semantic change.

## Classify every changed statement

Choose exactly one outcome per statement.

### 1. Locator-only change

The activation and enforced relation are unchanged; only names, organization,
formatting, or code location changed.

- Preserve the claim, authority, ID, and dependency edges.
- Update only source/anchor/check metadata and the inspected revision.
- Record enough context to distinguish a move from re-created but different logic.

### 2. Intended semantic change

An adopted standard, explicit project decision, or current human ruling authorizes the
new relation.

- Update the canonical claim and cite the authority for the change.
- Reconcile its decision-tree branch, activation, dependencies, derived `INV`/`REJ`,
  exported `OUT`, and direct consumers.
- Preserve the ID when the proposition retains the same role. During prototype
  cleanup, delete or replace obsolete IDs without maintaining a retired-ID ledger;
  explicitly migrate any external references to adopted IDs.
- Do not infer intendedness from the implementation change itself.

### 3. Implementation mismatch

The intended relation is unchanged, but the current constraint or verifier check
enforces a different or weaker relation.

- Preserve the specification claim and authority.
- Do not rewrite, weaken, or delete the claim to match the implementation.
- Report the mismatch separately from specification content: affected IDs, intended
  relation, enforced relation, activation, and consequence.
- Do not edit implementation during a specification-only task unless separately asked.

### 4. Unresolved intent

Evidence is insufficient or conflicting, and no authority establishes which relation
is intended.

- Preserve the prior claim as provisional when it remains the current candidate; do
  not silently replace it with the newest implementation behavior.
- Add one narrow `GAP` naming the exact decision, affected IDs, evidence, and owner.
- Use `disputed` only when an asserted claim conflicts with an adopted source and the
  project has not resolved the conflict.
- Leave the statement unreconciled in the handoff.

## Evidence-loss cases

Treat these as stronger signals than an ordinary locator edit.

### Missing anchor or enforcement

Search the bounded implementation path for the relation under a new symbol or
structure. If it moved unchanged, classify it as locator-only. If no enforcing site
exists, classify it as an implementation mismatch or unresolved intent; never hide the
loss by deleting the statement. Reflect the actual lower binding in metadata, but do
not present that downgrade as successful reconciliation.

### Failed executable check

First state the exact projection the check decides. Determine whether the projection,
the artifact, or the check changed. Fix an incorrect check; otherwise classify the
semantic or shape drift above. Never weaken a check merely to make it pass, and never
treat a shape check as proof of a broader semantic relation.

### Profile applicability change

Classify each in-scope statement as `matched`, `changed`, `absent`, or `not checked` for
the current profile. `Absent` means the relation or feature is not present; it does not
by itself mean the profile correctly rejects or excludes it.

### Dependency change

When an `ASM`, activation predicate, or `OUT` changes, re-evaluate every dependent
statement and direct consumer. A locally unchanged equation may acquire a different
meaning when its domain or imported guarantee changes.

## Revision discipline

Advance a module's implementation revision or mark it reconciled only after every
in-scope statement has one of the four classifications. For partial work, state the
checked subset and leave the remaining applicability `not checked`; do not make the
entire module appear current.

## Handoff

Report:

- prior and current implementation/profile revisions;
- statement IDs grouped by the four outcomes;
- metadata, claims, dependencies, and consumers changed;
- unresolved `GAP` IDs and their required decisions;
- implementation mismatches separately from specification edits;
- any statement or profile portion not checked.
