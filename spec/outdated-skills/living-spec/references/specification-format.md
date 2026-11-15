# Living Specification Format

Use this format for proof-system specifications. The main body is a short technical
contract for humans and machines. Provenance is consolidated at the bottom.

`../STYLE.md` governs visual and editorial choices. This reference defines the
structural schema when the style guide leaves room for choice.

## Specification set

For a multi-file specification:

```text
spec/
|-- INDEX.md
|-- notation.md             # only shared symbols used by several modules
|-- <module>.md
`-- <subsystem>/
    `-- <module>.md
```

`INDEX.md` contains:

1. specification revision and implementation revision(s);
2. active proof-system/machine profiles;
3. module ID, path, scope, and status;
4. the module dependency DAG;
5. global open gaps.

The index is not an implicit source of assumptions. Every module declares its own imports.

## Statement vocabulary

| Prefix | Meaning |
|---|---|
| `IN` | admitted input domain or boundary value |
| `ASM` | guarantee imported from another module |
| `REL` | semantic relation enforced by this module |
| `REQ` | non-relational requirement enforced by this module |
| `INV` | property preserved across a state transition or proof layer |
| `REJ` | condition under which acceptance is impossible |
| `OUT` | state or argument effect exported across a real component boundary |
| `GAP` | unresolved decision or missing evidence; not an asserted defect |

## Module template

```markdown
# <MODULE-ID>: <title>

> <one-line scope and exclusions>

`*` marks a provisional relation whose support is implementation-only, incomplete or
conflicting, or whose intendedness remains open.

## Guarantee

<Two to five terse lines describing the component contract.>

## Symbols

- `<symbol> : <domain>` — <definition>

## Inputs

- **IN-<MODULE>-001 — <name>.** `<domain or input predicate>`

## Assumptions

- **ASM-<MODULE>-001* — <name>.** `<imported proposition>`

## Decision tree

> Under `ASM-<MODULE>-...`. Navigation view only; leaf IDs name canonical statements.

- **`execute = 0`.** `<inactive relation or explicit scope boundary>`
- **`execute = 1`.**
  - **`<reachability predicate> = false`.** `<REJ-ID or unreachable under ASM-ID>`
  - **`<reachability predicate> = true`.** `<next selector, requirement, or output IDs>`

## Relations

### REL-<MODULE>-001* — <name>

`<atomic enforced relation>`

## Requirements

### REQ-<MODULE>-001* — <name>

`<non-relational enforced requirement>`

## Preserved invariants

- **INV-<MODULE>-001 — <name>.**
  `<P(state_i) ⇒ P(state_{i+1}) or layer analogue>`

## Rejections

- **REJ-<MODULE>-001 — <name>.** `<condition ⇒ no accepting proof>`

## Outputs

- **OUT-<MODULE>-001 — <name>.** `<exported proposition or public binding>`

## Open boundary

- **GAP-<MODULE>-001 — <name>.** `<one decision or missing fact>`

## Metadata

- spec revision: `<revision>`
- implementation: `<repository>@<commit>[+dirty]`
- profile: `<profile-id>`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-<MODULE>-001` | normative \| provisional | — | — | prose \| located \| pinned \| checked | `<stable locator>` | `<typed anchor or check>` |
| `ASM-<MODULE>-001` | normative \| provisional | — | `<OUT-ID or external boundary>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `REL-<MODULE>-001` | normative \| provisional \| disputed | `<predicate or always>` | `<IDs>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `REQ-<MODULE>-001` | normative \| provisional \| disputed | `<predicate or always>` | `<IDs>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `INV-<MODULE>-001` | normative \| provisional \| disputed | `<predicate or always>` | `<IDs>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `REJ-<MODULE>-001` | normative \| provisional \| disputed | `<predicate>` | `<IDs>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `OUT-<MODULE>-001` | normative \| provisional | — | `<IDs>` | `<derived>` | `<stable locator>` | `<typed anchor or check>` |
| `GAP-<MODULE>-001` | open | — | `<affected IDs/scope; owner>` | — | `<conflicting/insufficient evidence>` | — |
```

See `spec/METADATA.md` for field semantics. Every main-body ID has exactly one
combined metadata row. A module may split the columns into two tables only when the
combined form is materially less readable; every ID must then occur once in each
applicable table. Group ranges only when every field is identical and no per-ID
traceability is lost.

## Formula conventions

- Define integer and field domains explicitly: `u32 = [0, 2³²)`, `F = GF(p)`.
  Use membership such as `pc ∈ u32` rather than repeating the corresponding bounds.
- Use `x ← expression` for architectural state assignment: the right-hand side uses
  the pre-transition value and unassigned architectural locations remain unchanged.
  Use `x'` only when both state values must remain explicit in one mathematical
  relation. Use subscripts for row/round/layer indices.
- Use `=` for equality in the declared domain; write `= (mod n)` when needed.
- Use `∧`, `∨`, `¬`, `⇒`, and `⇔` consistently.
- Quantify non-local variables: `∀ i ∈ [0, n)`.
- Define named predicates under `Symbols`.
- State selector domains and inactive behavior.
- State first/last-row, padding, chunk, transcript, and recursion boundaries where
  applicable.

## Quality gate

- IDs are unique and references resolve.
- Every main-body ID has one row in each applicable metadata table.
- Symbols and domains are defined.
- Decision trees test the outer activation/mode gate before local selectors.
- Assumptions define tree context rather than runtime branches.
- Decision-tree branches are mutually exclusive and exhaustive within their stated domain.
- Every decision-tree leaf resolves to statement IDs or an explicit scope boundary.
- Relations and requirements are activated or explicitly unconditional.
- Assumptions identify exact exporting statements.
- Authority and binding are not conflated.
- Typed anchors use symbols, delimited regions, or counted patterns rather than line numbers.
- Regression coverage distinguishes semantic violations from shape-only detection.
- Public outputs and verifier acceptance conditions are explicit.
- Provisional claims and conflicts remain visible.
- No implementation observation is labeled normative without authority.
