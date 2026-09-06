# LOOKUP-REL: Weighted logarithmic-derivative lookup

> Defines one lookup instance. The caller owns the meaning and construction of its
> query rows, table rows, coefficients, and table binding.

## Symbols

- `F = GF(p)` — the base field; integer counts are embedded in `F`.
- `E` — the field containing the lookup challenges and accumulators.
- `Q ⊆ F^w` — the finite sequence of query rows.
- `T = (T[0], …, T[n − 1]) ⊆ F^w` — the finite sequence of table rows.
- `a(q)` — the nonnegative integer weight of query occurrence `q`.
- `m[i]` — the nonnegative integer multiplicity assigned to table occurrence `T[i]`.
- `enc_α(r) = Σ_(j = 0)^(w − 1) α^j r[j]` — compression of one row.

## Inputs

- **IN-LOOKUP-REL-001 — Lookup instance.** One instance fixes `F`, `E`, `w`, `Q`, `T`,
  `a`, and `m`. The caller constrains their concrete values and publishes bounds
  sufficient for `REQ-LOOKUP-SND-001`.
- **IN-LOOKUP-REL-002 — Table binding.** Before the lookup challenges are sampled, the
  verifier binds `T` either through an authenticated commitment or by evaluating a
  deterministic table definition fixed by the calling relation.

## Assumptions

- **ASM-LOOKUP-001 — Query provenance.** The calling relation constrains every `q`
  and `a(q)` to the computation whose table membership it claims.
- **ASM-LOOKUP-002 — Reduction correctness.** The consuming proof establishes that
  the terminal numerator and denominator are the reduction of all terms in
  `REQ-LOOKUP-006`. This is discharged by the proof protocol that implements the
  lookup reduction.

## Requirements

### REQ-LOOKUP-REL-001 — Row compression

After `Q` and `T` are bound, sample `(α, β) ∈ E²` together and encode every row
with `enc_α`. Column order and width are fixed by `IN-LOOKUP-REL-001`; the proof
cannot choose them.

### REQ-LOOKUP-REL-002 — Weighted multiplicities

For every row `r ∈ F^w`, the intended integer relation is

`Σ_(i : T[i] = r) m[i] = Σ_(q ∈ Q : q = r) a(q)`.

When `T` contains repeated rows, only the sum of their multiplicities is fixed. The
witness may place that sum on any one occurrence and set the others to zero.

### REQ-LOOKUP-REL-003 — Activated queries

A query with `a(q) = 0` contributes nothing. A query with `a(q) > 0` contributes that
many copies of its row. The calling relation, not this argument, decides how `a(q)` is
derived and when it may be nonzero.

### REQ-LOOKUP-006 — Rational identity

Using the `β` sampled with `α` in `REQ-LOOKUP-REL-001`, form

`A = Σ_(q ∈ Q) a(q)/(β + enc_α(q)) − Σ_(i = 0)^(n − 1) m[i]/(β + enc_α(T[i]))`.

The lookup relation requires `A = 0`. The verifier evaluates this requirement through
the projective pairs in [verifier.md](verifier.md), without dividing in `E`.

## Output

- **OUT-LOOKUP-001 — Weighted table membership.** Subject to
  `REQ-LOOKUP-SND-001..003`, acceptance implies `REQ-LOOKUP-REL-002` for the supplied
  instance.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-LOOKUP-REL-001` | normative | one lookup instance | — | standalone lookup interface |
| `IN-LOOKUP-REL-002` | normative | one lookup instance | `IN-LOOKUP-REL-001` | authenticated-table boundary |
| `ASM-LOOKUP-001` | normative | every query | external boundary: calling relation | query provenance |
| `ASM-LOOKUP-002` | normative | proof acceptance | discharged by `REQ-GKR-VER-005` | reduction correctness |
| `REQ-LOOKUP-REL-001` | normative | one lookup instance | `IN-LOOKUP-REL-001..002` | [Haböck, eprint 2022/1530](https://eprint.iacr.org/2022/1530); project row compression |
| `REQ-LOOKUP-REL-002` | normative | one lookup instance | `IN-LOOKUP-REL-001`, `ASM-LOOKUP-001` | [Haböck, eprint 2022/1530](https://eprint.iacr.org/2022/1530), Lemma 4 and Equation 13 |
| `REQ-LOOKUP-REL-003` | normative | every query | `ASM-LOOKUP-001`, `REQ-LOOKUP-REL-002` | weighted form of `REQ-LOOKUP-REL-002` |
| `REQ-LOOKUP-006` | normative | one lookup instance | `REQ-LOOKUP-REL-001..003`, `ASM-LOOKUP-002` | [Haböck, eprint 2022/1530](https://eprint.iacr.org/2022/1530), Lemmas 4–5 |
| `OUT-LOOKUP-001` | normative | accepted lookup instance | `REQ-LOOKUP-REL-001..003`, `REQ-LOOKUP-006`; `REQ-LOOKUP-SND-001..003` | derived from the logarithmic-derivative identity |
