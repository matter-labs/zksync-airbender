# LOOKUP-SND: Lookup soundness

> States the conditions under which the rational identity implies weighted table
> membership. Concrete circuits must instantiate the bounds; they are not listed here.

## Imports

- `arguments/lookups/relation.md`
- `arguments/lookups/verifier.md`

## Baseline

[Haböck, *Multivariate lookups based on logarithmic
derivatives*](https://eprint.iacr.org/2022/1530), Lemma 4 and the sentence following
Equation 13, proves that equality of logarithmic derivatives determines the
multiplicity of each field value when the characteristic exceeds the total
multiplicity admitted by the hypercube. [Papini and Haböck, *Improving logarithmic derivative
lookups using GKR*](https://eprint.iacr.org/2023/1284) proves the projective-pair
reduction used by `REQ-LOOKUP-VER-002..004`.

For scalar values, the identity

`Σ_q a(q)/(β + q) = Σ_i m[i]/(β + T[i])`

as a rational function of `β` fixes the summed coefficient of every distinct value.
Repeated table rows therefore require the per-value multiplicity rule of
`REQ-LOOKUP-REL-002`, not a separate count on every table occurrence.

## Requirements

### REQ-LOOKUP-SND-001 — Characteristic bound

Interpret `a(q)` and `m[i]` as nonnegative integer counts embedded in `F`. Require

`Σ_q a(q) < p` and `Σ_i m[i] < p`.

These sufficient bounds prevent two unequal integer multiplicities from becoming
equal modulo the characteristic. The calling circuit must publish and enforce bounds
that imply them for every instantiated lookup. In the supported circuits, query
activations are Boolean, so the compiled maximum query count times trace length
supplies the query-side bound; the selected table and multiplicity relation must supply
the table-side bound. The standalone relation permits arbitrary nonnegative integer
weights satisfying both bounds.

### REQ-LOOKUP-SND-002 — Pole rejection

Require the terminal denominator of `REQ-LOOKUP-VER-004` to be nonzero. Sampling
`β` without excluding the pole set introduces completeness error, but accepting a
zero denominator would invalidate the inference from the accumulated numerator.

### REQ-LOOKUP-SND-003 — Joint row-compression bound

Assume `w ≥ 1` and let `s = |Q| + n` be the number of rational terms. Clear all
denominators in `REQ-LOOKUP-006`. If the weighted tuple-multiplicity relation fails,
`REQ-LOOKUP-SND-001` and injectivity of `enc_α(r)` as a polynomial in `α` make the
cleared numerator a nonzero polynomial in `(α, β)`. Its total degree is at most

`(s − 1) · max(1, w − 1)`.

When `α` and `β` are sampled independently and uniformly from `E`,
Schwartz–Zippel therefore gives

`Pr[failed membership passes N = 0] ≤ (s − 1) · max(1, w − 1) / |E|`.

The separate check `D ≠ 0` rejects sampled poles. A calling soundness budget charges
this bound for every independently sampled lookup instance.

## Output

- **OUT-LOOKUP-SND-001 — Lookup soundness.** Under `REQ-LOOKUP-SND-001..003`, and
  except with the reduction protocol's own error and the bound of
  `REQ-LOOKUP-SND-003`, acceptance implies `REQ-LOOKUP-REL-002`.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `REQ-LOOKUP-SND-001` | normative | one lookup instance | `IN-LOOKUP-REL-001`, `REQ-LOOKUP-REL-002`, `REQ-LOOKUP-006` | [Haböck, eprint 2022/1530](https://eprint.iacr.org/2022/1530), Lemma 4 and the sentence following Equation 13; weighted form is project-derived |
| `REQ-LOOKUP-SND-002` | normative | terminal check | `REQ-LOOKUP-VER-004` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284), terminal `q_1(+1)q_1(−1) ≠ 0` check; [Haböck, eprint 2022/1530](https://eprint.iacr.org/2022/1530), Remark 3 for completeness at poles |
| `REQ-LOOKUP-SND-003` | normative | one lookup instance | `REQ-LOOKUP-SND-001..002`, `REQ-LOOKUP-REL-001..003`, `REQ-LOOKUP-006` | project row compression; multivariate Schwartz–Zippel |
| `OUT-LOOKUP-SND-001` | normative | accepted lookup instance | `REQ-LOOKUP-SND-001..003` | derived from the logarithmic-derivative identity and joint row-compression bound |
