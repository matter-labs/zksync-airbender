# Specification metadata

> Metadata supports provenance, dependency analysis, drift detection, and future
> automation. It does not replace the human-readable claim in each module body.

## Record model

Each statement has one permanent ID. The statement beside that ID in the module body
is its claim. The final metadata section supplies the remaining fields.

| Field | Meaning |
|---|---|
| `id` | permanent `KIND-MODULE-NNN` identifier |
| `authority` | why the project treats the claim as intended |
| `activation` | predicate/domain under which the claim applies, or `always` |
| `depends` | exact statement IDs required to interpret or derive the claim |
| `discharged-by` | for `ASM`, the exact exporting `OUT` ID or an explicit external assumption |
| `source` | standard, project decision, or implementation evidence supporting the claim |
| `anchor` | typed, machine-resolvable implementation location |
| `check` | optional executable assertion over a machine-observable projection |
| `binding` | derived strength of the implementation connection |
| `exported` | whether an `OUT` crosses a system/public boundary rather than only a module boundary |
| `tags` | optional classification, such as a bug class or W2 obligation |
| `superseded-by` | permanent replacement for a retired ID |

Do not duplicate the claim in metadata. Do not delete or renumber an established ID;
retire it with `superseded-by`.

## Authority

Authority and implementation binding are independent.

| Authority | Meaning |
|---|---|
| `normative` | adopted standard, explicit project decision, or designated project specification |
| `provisional` | inferred from consistent implementation, tests, history, or architecture evidence |
| `disputed` | conflicts with an adopted source and awaits a project decision |
| `open` | `GAP` only; no claim has been selected |

A normative statement requires an authority source. Implementation evidence alone
cannot make a statement normative.

## Activation

Every `REQ`, `INV`, and `REJ` states its activation predicate. Use `always` only when
the relation is genuinely unconditional within the module domain.

Activation is separate from dependency:

- `activation` answers when the statement applies;
- `depends` answers which other statements give it meaning or support.

## Sources and anchors

`source` is for humans. Prefer stable locators:

- `standard:<document>#<section>`;
- `decision:<id>`;
- `repo:<path>#<symbol>@<revision>`;
- `derived:<statement-ids>`.

`anchor` is for future drift tooling. Supported conceptual kinds are:

| Kind | Use |
|---|---|
| `symbol` | named function, method, type, constant, or generated verifier entrypoint |
| `region` | explicitly delimited generated-code span with no stable symbol |
| `pattern` | expected set/count of structurally repeated matches |

Line numbers may supplement an anchor but never define it. A symbol move should not
look like a semantic deletion.

## Binding

`binding` is derived from available machinery; it is not a confidence claim written
by the statement author.

| Binding | Meaning |
|---|---|
| `checked` | an executable assertion decides the stated machine-observable relation |
| `pinned` | a normalized content hash detects semantic drift of every declared anchor |
| `located` | typed anchors exist, but no accepted content hash is maintained |
| `prose` | only human-readable sources/evidence exist |

An executable shape check does not make a broader semantic claim `checked`. Binding
must describe the actual projection decided by the check.

The current specification has no pin/check tool. Its implementation-linked statements
are therefore at most `located`. A future tool may add a generated lockfile; the
lockfile must not become normative content.

## Assumptions and outputs

An `ASM` either names `discharged-by: OUT-...` or says `external:<boundary>`. A module
name alone is temporary metadata while the exporting statement is not yet written.

An `OUT` distinguishes an internal cross-module export from a system/public boundary
when that distinction matters.

## Gaps

A `GAP` records:

| Field | Meaning |
|---|---|
| `question` | one decision or missing fact |
| `affects` | exact IDs or scope blocked by the gap |
| `evidence` | conflicting or insufficient sources |
| `owner` | `human` or a named decision owner |

Gaps have `authority = open`; activation and binding do not turn them into claims.

## Regression linkage

For a confirmed historical defect, `tags` may name a stable bug class. Record which
statement the defective implementation violates; do not infer coverage merely because
the statement concerns the same component.

- `semantic`: the claim itself is false under the defect;
- `shape`: an executable count, width, or activation check detects only that projection;
- `none`: no current statement excludes the defect.

Shape agreement does not imply semantic agreement. A future regression index may map
bug IDs to statement IDs and these coverage levels; it is audit evidence, not normative
specification content.

## Current Markdown encoding

Use two bottom tables for ordinary modules. The split keeps semantic dependency data
readable while allowing implementation traces to be detailed. Every statement ID
appears once in each applicable table.

| ID | Authority | Activation | Depends / discharged by |
|---|---|---|---|
| `REQ-X-001` | provisional | `execute` | `ASM-X-001` |

| ID | Binding | Source | Anchor / check |
|---|---|---|---|
| `REQ-X-001` | located | `repo:path#symbol@rev` | `symbol:path#symbol` |

Keep longer gap questions in the readable `Open boundary` section; use their metadata
row for `affects`, evidence, and owner. Optional fields may be omitted when empty.

This table is the current transport, not a permanent serialization decision. A future
machine-readable representation must preserve the same semantics without forcing
YAML-like records into the main reading flow.
