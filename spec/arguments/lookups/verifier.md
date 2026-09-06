# LOOKUP-VER: Lookup verifier obligations

> Evaluates the rational identity of one lookup instance. The caller decides how many
> instances exist and what each instance means.

## Imports

- `arguments/lookups/relation.md`

## Requirements

### REQ-LOOKUP-VER-001 — Challenge and table binding

Bind `IN-LOOKUP-REL-001`, `IN-LOOKUP-REL-002`, and every value that enters
`REQ-LOOKUP-006` before drawing `α` and `β` together. No binding step occurs between
the two draws. Use the same `(α, β)` in every term of the instance.

### REQ-LOOKUP-VER-002 — Fraction pairs

Represent the terms of `REQ-LOOKUP-006` as

`q ↦ (a(q), β + enc_α(q))`

`T[i] ↦ (−m[i], β + enc_α(T[i]))`.

A pair `(n, d)` represents `n/d`; no division is performed.

### REQ-LOOKUP-VER-003 — Pair accumulation

Starting from `(N, D) = (0, 1)`, combine every term pair `(n, d)` by

`N ← N d + n D`

`D ← D d`.

Any tree or batching schedule is admissible only if it preserves this projective sum
and discharges `ASM-LOOKUP-002`.

### REQ-LOOKUP-VER-004 — Terminal identity

Accept only when

`N = 0 ∧ D ≠ 0`.

The numerator check enforces `A = 0`; the denominator check rejects a pole. Checking
only `N = 0` is insufficient.

### REQ-LOOKUP-VER-005 — Instance independence

Apply `REQ-LOOKUP-VER-004` separately to every lookup instance declared by the
caller. Acceptance of one instance does not discharge another.

## Rejections

- **REJ-LOOKUP-VER-001 — Unbound input.** Reject if a query, table, coefficient, or
  multiplicity used by the reduction was not bound before its challenge.
- **REJ-LOOKUP-VER-002 — Pole.** Reject if the accumulated denominator is zero.
- **REJ-LOOKUP-VER-003 — Identity mismatch.** Reject if the accumulated numerator is
  nonzero.

## Output

- **OUT-LOOKUP-VER-001 — Accepted rational identity.** Acceptance establishes
  `REQ-LOOKUP-006` for each declared instance and discharges `ASM-LOOKUP-002`.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `REQ-LOOKUP-VER-001` | normative | one lookup instance | `IN-LOOKUP-REL-001..002`, `REQ-LOOKUP-REL-001`, `REQ-LOOKUP-006` | Fiat–Shamir binding of the lookup challenges |
| `REQ-LOOKUP-VER-002` | normative | every lookup term | `REQ-LOOKUP-006` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284) |
| `REQ-LOOKUP-VER-003` | normative | one lookup instance | `REQ-LOOKUP-VER-002` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284), projective pair addition |
| `REQ-LOOKUP-VER-004` | normative | one lookup instance | `REQ-LOOKUP-006`, `REQ-LOOKUP-VER-003` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284), terminal check |
| `REQ-LOOKUP-VER-005` | normative | every declared instance | `REQ-LOOKUP-VER-004` | independent conjunction of lookup instances |
| `REJ-LOOKUP-VER-001` | normative | verifier input binding | derived from `REQ-LOOKUP-VER-001` | derived from `REQ-LOOKUP-VER-001` |
| `REJ-LOOKUP-VER-002` | normative | terminal check | derived from `REQ-LOOKUP-VER-004` | derived from `REQ-LOOKUP-VER-004` |
| `REJ-LOOKUP-VER-003` | normative | terminal check | derived from `REQ-LOOKUP-VER-004` | derived from `REQ-LOOKUP-VER-004` |
| `OUT-LOOKUP-VER-001` | normative | accepted lookup instance | `REQ-LOOKUP-VER-001..005`; discharges `ASM-LOOKUP-002` | derived from `REQ-LOOKUP-VER-001..005` |
