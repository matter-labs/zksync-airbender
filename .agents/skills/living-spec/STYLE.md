# Living Specification Style

> Status: experimental. This guide records the current visual and editorial target.
> It is expected to change as the baseline improves. Human direction overrides it.

## Design target

A specification module should be:

- readable top-to-bottom by an engineer unfamiliar with its metadata scheme;
- terse enough to compare directly with constraints or verifier code;
- precise enough to translate into assertions or prover obligations;
- modular enough to review after replacing its named assumptions with axioms.

Optimize first for understanding the component, then for traceability. Stable IDs and
metadata support the document; they must not dominate it.

## Decision trees as the reading map

When a relation branches on modes, selectors, input classes, or boundary conditions,
present a shallow decision tree before the detailed statements. The tree is the
primary human navigation view; the identified statements remain the canonical claims.

- Order branches from coarse semantic gates to local behavior: activation or mode,
  reachability, decode/selector class, transformation, then output or rejection. For
  machine-cycle relations, test `execute` first unless the module establishes a
  different outer gate.
- State imported assumptions above the tree. Do not turn `ASM holds` versus `ASM does
  not hold` into runtime branches; the tree is interpreted under those assumptions.
- Partition the declared input domain into mutually exclusive branches. Cover the
  domain exhaustively, or mark the omitted branch as an explicit boundary or `GAP`.
- End each leaf with the controlling `ASM`, `REQ`, `INV`, `REJ`, or `OUT` ID. A leaf
  may instead name an explicit out-of-scope boundary.
- Distinguish `rejects`, `unreachable under <ASM>`, `inactive/padding relation`, and
  `out of scope`. Never use `irrelevant` without stating which of these it means.
- Keep equations and complete predicates in their canonical statement or case table.
  Do not create a second, subtly different claim inside the tree.
- Use nested Markdown bullets with bold branch predicates. Prefer several shallow
  trees over one deeply nested tree. Use a compact case table when it expresses the
  same partition more clearly.

A reviewer should be able to walk every branch first, then inspect only the leaf IDs
needed for formal detail and provenance.

## Page shape

Use this reading order unless the component needs a clearly better one:

1. `# <MODULE-ID>: <title>`
2. one-line scope and exclusions;
3. short guarantee summary;
4. symbols and inputs needed to read the mathematics;
5. imported assumptions;
6. decision tree when the relation has material branches;
7. central operation/relation, preferably as equations or a compact case table;
8. locally enforced requirements;
9. preserved invariants, rejection cases, and exported outputs when meaningful;
10. open boundary;
11. final metadata section mapping each ID to status, dependencies, and evidence.

A reader who stops before `Metadata` should still understand what the component is
supposed to do.

## Statement presentation

- Give each independently checkable statement one stable ID and a short technical
  name: `REQ-ADD-001 — Destination value`.
- Put the equation or predicate immediately after its heading. Add at most the prose
  needed to define cases, arithmetic domain, activation, or boundary behavior.
- Use a table when one relation has several instruction/opcode cases with the same
  columns.
- Use bullets for short assumptions, invariants, rejections, outputs, and gaps. Use a
  subsection when a statement needs equations or multiple cases.
- Keep IDs visible but secondary: a heading must remain meaningful without knowing the
  ID taxonomy.
- Prefer one proposition per ID. Do not split one small equation into several records
  merely to increase granularity.

## Mathematics

- Define every non-obvious symbol near first use.
- State domains and arithmetic explicitly: integer, field, bit-vector, or modulo
  `2^n`.
- For architectural state transitions, use `x <- expression`. The right-hand side
  denotes the pre-transition value, and unassigned architectural locations remain
  unchanged. Use a primed symbol only when the relation genuinely needs both state
  values as simultaneous mathematical objects.
- State activation and inactive behavior when a selector gates a relation.
- State boundary cases: first/last row, overflow, padding, segment edges, transcript
  order, and recursion roots/leaves when applicable.
- Prefer short inline formulas and compact display equations. Use notation that a
  human can read without decoding a custom mini-language.
- Use `=>` only for implication and `<=>` only when both directions are intended.

Whether the project should standardize on ASCII formulas or LaTeX is still open.
Current documents use ASCII-style formulas for easy ingestion.

## Prose and tone

- Technical, direct, and present tense.
- Short sentences; minimal rationale in normative sections.
- Use concrete verbs: `equals`, `binds`, `reads`, `writes`, `rejects`, `preserves`.
- Avoid undefined evaluative words such as `valid`, `correct`, `proper`, or
  `consistent`; name the predicate they abbreviate.
- Distinguish what the proof enforces from what the honest prover computes.
- Put lengthy rationale, audit findings, and implementation walkthroughs elsewhere.

## Metadata

Metadata belongs at the bottom. Use one combined row per statement ID so a reviewer
can see semantics and implementation traceability together:

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| stable ID | intendedness | applicability | exact claim edges | implementation grip | human locator | typed machine locator or executable assertion |

Split this into semantic and implementation tables only when the combined table is
materially harder to review. Preserve one-to-one rows and identical IDs across both
tables when split.

`spec/METADATA.md` defines these fields. In particular, authority and binding are
independent: a normative claim may be unpinned, while a provisional implementation
observation may be mechanically checked.

Do not repeat `status`, `source`, and `depends` fields under every main-body heading.
Document-level revision, implementation revision, and active profile also belong in
the metadata section unless they materially affect how the opening scope is read.

## Uncertainty

- Mark only genuinely uncertain semantics `provisional`: implementation-only
  inferences, incomplete or conflicting evidence, or unresolved intendedness. A
  relation aligned with an adopted standard, explicit human direction, or convergent
  constraint, architecture, test, and human evidence may be normative for its stated
  profile. When a module mixes provisional and adopted relations, append a visible
  `*` to each provisional main-body ID label and define the marker once near the top.
  The stable ID itself excludes the marker, so metadata and cross-references remain
  `REQ-X-001`.
- Express one unresolved decision per `GAP`. A gap is not a requirement or a finding.
- Map every provisional claim, or one clearly bounded provisional group, to the `GAP`
  that explains what prevents promotion.
- Put a short draft warning near the title only when the entire module is unreliable or
  stale; do not blanket every page with warnings.
- Never hide uncertainty by selecting the behavior that happens to appear most often
  in code.
- A regression link names the exact statement the defective implementation violates.
  Label shape-only detection separately from semantic exclusion.

## Preferred example

```markdown
### REQ-ADD-001* — Destination value

For an active row:

`rd <- (rs1 + rs2 + imm) mod 2^32`.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-ADD-001` | provisional | `is_add` | `ASM-ADD-001..003`; `GAP-ADD-001` | located | `repo:path#symbol@revision` | `symbol:path#symbol` |
| `GAP-ADD-001` | open | — | affects `REQ-ADD-001`; owner: human | — | no adopted relation identified | — |

## Open boundary

- **GAP-ADD-001 — Intended arithmetic relation.** Adopt or replace the current
  implementation-only candidate relation.
```

## Avoid

- a wall of metadata before the reader encounters the component relation;
- YAML-like `status/source/depends` blocks interleaved with every equation;
- prose-only claims such as “the instruction is handled correctly”;
- implementation variable names without a semantic definition;
- one file spanning unrelated proof contexts merely to reduce file count;
- duplicating another module's requirement instead of importing its output;
- duplicating full equations in both a decision tree and their canonical statements;
- polishing unresolved behavior into apparently normative language.

## Open style decisions

The following choices are intentionally unsettled:

- ASCII formulas versus a restricted LaTeX subset;
- the final Markdown encoding of the metadata model;
- when derived `REJ` and `OUT` statements add enough audit value to retain;
- ideal module size and instruction-family granularity;
- whether shared notation deserves `spec/notation.md`;
- how much W2 cross-reference belongs in ordinary relation modules;
- which parts of the style can later be checked automatically.

Do not mass-rewrite the specification when one of these changes. Apply the new choice
to the active module, confirm it with the human, then reconcile older modules
incrementally.

## Evolution rule

Treat accepted modules and explicit human feedback as the design evidence for this
guide. When a recurring presentation choice proves useful, record it here. When a
rule obstructs understanding, weaken or remove it. Promote this guide from
experimental only after several representative modules—machine relations, global
arguments, transcript/protocol relations, and recursion—read well under the same
conventions.
