# TABLE-RNG: Verifier-derived range tables

> Defines the two virtual range tables shared by supported circuits. Circuit modules
> decide which values are queried and how many queries exist.

## Imports

- `arguments/lookups/relation.md`

## Symbols

- `n = 2^k` — setup-column length.
- `T_b = [0, 1, …, 2^b − 1, 0, …, 0]` — the width-`b` ramp followed by zeros to
  length `n`, requiring `k ≥ b`.

## Input

- **IN-LOOKUP-002 — Virtual range tables.** The range tables are not committed setup
  columns. Their definitions and `n` are fixed by the calling circuit, and the
  verifier reconstructs their evaluations.

## Requirements

### REQ-TABLE-RNG-001 — Virtual table construction

Construct the 16-bit table as `T_16` and the timestamp-limb table as `T_19`. Padding
zeros are ordinary repeated table rows; their multiplicities follow
`REQ-LOOKUP-REL-002`.

### REQ-LOOKUP-004 — 16-bit range admission

For every caller-declared 16-bit query `x`, require

`x ∈ T_16`, equivalently `0 ≤ x < 2^16` under the canonical integer embedding in
the base field.

### REQ-LOOKUP-005 — Timestamp-limb range admission

For every caller-declared timestamp-limb query `t`, require

`t ∈ T_19`, equivalently `0 ≤ t < 2^19` under the canonical integer embedding in
the base field.

### REQ-TABLE-RNG-002 — Multilinear extension

At `pt ∈ E^k`, the multilinear extension of `T_b` is

`(Σ_(j = 0)^(b − 1) 2^j pt[j]) · (Π_(j = b)^(k − 1) (1 − pt[j]))`.

A verifier that does not open a committed range column must derive its claimed
evaluation from this expression.

## Output

- **OUT-TABLE-RNG-001 — Bound range-table evaluations.** For `b ∈ {16, 19}`, the
  verifier-derived evaluation is the evaluation of the zero-padded table `T_b`.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-LOOKUP-002` | normative | virtual range-table use | — | supported verifier-derived setup interface |
| `REQ-TABLE-RNG-001` | normative | virtual range-table construction | `IN-LOOKUP-002` | supported virtual range tables |
| `REQ-LOOKUP-004` | normative | caller-declared 16-bit query | `ASM-LOOKUP-001`, `REQ-TABLE-RNG-001` | 16-bit virtual range table |
| `REQ-LOOKUP-005` | normative | caller-declared timestamp-limb query | `ASM-LOOKUP-001`, `REQ-TABLE-RNG-001` | 19-bit timestamp virtual range table |
| `REQ-TABLE-RNG-002` | normative | verifier-derived table evaluation | `REQ-TABLE-RNG-001` | multilinear extension of a zero-padded binary ramp |
| `OUT-TABLE-RNG-001` | normative | accepted derived setup evaluation | `REQ-TABLE-RNG-001..002` | derived from the virtual-table definition |
