# TABLE-FIX: Fixed semantic-table interface

> Defines what every fixed `TableType` must specify. Individual table relations are
> separate definitions selected by circuit modules.

## Input

- **IN-TABLE-FIX-001 — Table-type definition.** A fixed table type declares one
  stable class identifier, an ordered key/value payload schema, and a deterministic
  generator for its complete row set.

## Requirements

### REQ-TABLE-FIX-001 — Identifier uniqueness

Two distinct table types selected in the same setup must have distinct class
identifiers. The identifier is fixed before preprocessing and is not proof data.

### REQ-TABLE-FIX-002 — Complete generation

The generated row set contains every row admitted by the table type's stated relation
and no other row. Generation order may affect preprocessing layout but not membership.

### REQ-TABLE-FIX-003 — Query schema

A query to the table uses the same key/value field order and payload width as
`IN-TABLE-FIX-001`. If several table classes share an instance, append the identifier
according to `REQ-LOOKUP-001` before applying `REQ-LOOKUP-002`.

## Output

- **OUT-TABLE-FIX-001 — Fixed row class.** The table type exports a deterministic
  row class that a circuit may select for one lookup instance.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-TABLE-FIX-001` | normative | fixed table definition | — | supported `TableType` interface |
| `REQ-TABLE-FIX-001` | normative | two or more selected fixed table types | `IN-TABLE-FIX-001` | table namespace construction |
| `REQ-TABLE-FIX-002` | normative | fixed table generation | `IN-TABLE-FIX-001` | fixed-table generator contract |
| `REQ-TABLE-FIX-003` | normative | fixed-table query | `IN-TABLE-FIX-001`, `REQ-LOOKUP-001..002` | fixed-table query contract |
| `OUT-TABLE-FIX-001` | normative | completed fixed table definition | `REQ-TABLE-FIX-001..003` | derived from the fixed-table interface |
