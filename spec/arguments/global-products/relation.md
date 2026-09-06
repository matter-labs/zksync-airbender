# GP-REL: Fingerprinted multiset equality

> Defines one global-product instance. The caller owns the meaning, construction, and
> local constraints of the tuples placed on each side.

## Symbols

- `E` — the challenge and product field.
- `R`, `W` — finite multisets of tuples in `E^d`.
- `R_i`, `W_i` — caller-defined partitions whose multiset unions are `R` and `W`.
- `χ = (β, α_0, …, α_(d − 1)) ∈ E^(d + 1)` — the challenge vector.
- `enc_χ(e) = β + Σ_(j = 0)^(d − 1) α_j e[j]` — one tuple factor.

## Input

- **IN-GP-REL-001 — Product instance.** One instance fixes `E`, `d`, the tuple
  order, and the partitions admitted on each side. The caller constrains every tuple
  and fixes the partition inventory before `χ` is sampled.

## Assumption

- **ASM-GP-REL-001 — Tuple provenance.** The calling relations constrain every
  coordinate and activation condition of every tuple in `R` and `W`.

## Requirements

### REQ-GP-REL-001 — Tuple compression

After all tuple-producing values are bound, sample `χ` and encode every tuple with
`enc_χ`. Tuple width and coordinate order come from `IN-GP-REL-001`; the proof cannot
choose them.

### REQ-GP-REL-002 — Partition products

For every declared partition `i`, compute

`P_R[i] = Π_(e ∈ R_i) enc_χ(e)`

`P_W[i] = Π_(e ∈ W_i) enc_χ(e)`.

An empty partition has product `1`. A proof protocol may establish these products
directly or by a reduction, but must bind them to the tuples of that partition.

### REQ-GP-REL-005 — Aggregate products

Combine every declared partition exactly once:

`P_R = Π_i P_R[i]` and `P_W = Π_i P_W[i]`.

Associativity permits any aggregation tree. It does not permit omitting, duplicating,
or moving a partition between sides.

### REQ-GP-REL-004 — Product identity

The argument accepts only if

`P_R = P_W`.

## Output

- **OUT-GP-REL-001 — Multiset equality.** Under `ASM-GP-REL-001` and except with
  the error stated by `REQ-GP-SND-001`, acceptance implies
  `R = W` as multisets of tuples.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-GP-REL-001` | normative | one product instance | — | standalone product-argument interface |
| `ASM-GP-REL-001` | normative | every supplied tuple | external boundary: calling relation | tuple provenance |
| `REQ-GP-REL-001` | normative | one product instance | `IN-GP-REL-001`, `ASM-GP-REL-001` | fingerprinted tuple encoding |
| `REQ-GP-REL-002` | normative | every declared partition | `REQ-GP-REL-001` | product over encoded multiset elements |
| `REQ-GP-REL-005` | normative | one product instance | `REQ-GP-REL-002` | associativity of multiplication |
| `REQ-GP-REL-004` | normative | proof acceptance | `REQ-GP-REL-005` | fingerprinted multiset equality |
| `OUT-GP-REL-001` | normative | accepted product instance | `ASM-GP-REL-001`, `REQ-GP-REL-001..002`, `REQ-GP-REL-004..005`; `REQ-GP-SND-001` | derived from polynomial fingerprinting |
