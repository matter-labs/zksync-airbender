# TABLE-ENC: Lookup-table encoding

> Defines the common encoding used when one lookup instance contains rows from one or
> more table classes. A circuit owns the selected class inventory.

## Imports

- `arguments/lookups/relation.md`

## Symbols

- `n = 2^k` — setup-column length fixed by the calling circuit.
- `C` — ordered set of table classes selected by one lookup instance.
- `rows(c)` — ordered payload rows generated for class `c ∈ C`.
- `id(c)` — class identifier fixed independently of the proof.
- `payload(c)` — width of rows in `rows(c)`.

## Input

- **IN-TABLE-ENC-001 — Declared setup.** The calling circuit fixes `n`, `C`, every
  class identifier, payload schema, row generator, and class order. The proof cannot
  add, remove, reorder, or resize a class.

## Requirements

### REQ-LOOKUP-001 — Generic setup formation

Let `has_id = 1` exactly when `|C| > 1`, and let

`w = max_(c ∈ C) payload(c) + has_id`.

Encode a row of class `c` by placing its payload first, zero-padding it to the maximum
payload width, and appending `id(c)` exactly when `has_id = 1`. Thus one table class
has no ID column; two or more classes always have one, whether the classes are fixed,
program-derived, or verifier-derived.

Form `T` by concatenating `rows(c)` in the declared class order and append all-zero
rows until its length is `n`. Require the unpadded row count to be at most `n`.

### REQ-LOOKUP-002 — Fixed semantic-table admission

A query selecting fixed table class `c` supplies the key and value payload constrained
by the calling circuit, followed by the zero padding and optional class ID of
`REQ-LOOKUP-001`. The resulting row must equal a row produced by `rows(c)`.

The definition of `rows(c)` determines the table relation. This module does not infer
that relation from a query or from the table identifier.

### REQ-TABLE-ENC-001 — Deterministic setup

For fixed public inputs, `IN-TABLE-ENC-001` determines every setup row. Any committed
form and any verifier-reconstructed form of the same declared setup must evaluate to
the same table polynomial.

## Output

- **OUT-TABLE-ENC-001 — Encoded table instance.** The output is one width-`w`,
  length-`n` table sequence suitable as `T` in `IN-LOOKUP-REL-001`.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-TABLE-ENC-001` | normative | lookup setup construction | — | supported table-preprocessing interface |
| `REQ-LOOKUP-001` | normative | lookup setup construction | `IN-TABLE-ENC-001` | supported generic-setup encoding |
| `REQ-LOOKUP-002` | normative | fixed semantic-table query | `REQ-LOOKUP-001`, `ASM-LOOKUP-001` | supported fixed-table admission relation |
| `REQ-TABLE-ENC-001` | normative | lookup setup construction | `IN-TABLE-ENC-001`, `REQ-LOOKUP-001` | deterministic table preprocessing |
| `OUT-TABLE-ENC-001` | normative | completed lookup setup | `REQ-LOOKUP-001`, `REQ-TABLE-ENC-001` | derived from the table-encoding requirements |
