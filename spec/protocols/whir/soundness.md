# WHIR-SND: WHIR soundness

> The literature baseline for the opening proof, the deviations the production form
> makes against it, the shape of every per-round error term, and the two obligations
> that remain open. No proximity or query bound is instantiated for any selected
> parameter set at the assessed revision.

## Imports

- `protocols/whir/verifier.md`
- `protocols/sumcheck/soundness.md`
- `soundness/assumptions.md`

## Guarantee

None yet. The baseline analysis is parameterized and its instantiation for the selected
fields, schedules, and grinding stages is not recorded. The implementation chooses
query counts with a separate heuristic; it does not select the proximity slack or list
sizes needed to evaluate the theorem below.

## Symbols

- `lambda = 100` — the nominal security level of every selected set, in bits.
- `r_i = 2^(-rho_i)` — the rate of the round-`i` code.
- `delta_i ∈ (0, 1)` — the proximity parameter of the round-`i` code.
- `list_(i,s)` — a list-size bound at distance `delta_i` for the code after step `s`
  of round `i`; Theorem 5.2 requires one such bound for every `s ∈ [0, k_i]`.
- `eta_i` — slack below capacity, so a capacity-regime choice satisfies
  `delta_i < 1 − r_i − eta_i`.
- `d* = 3` — for `w_hat_0(Z, X) = Z·eq(z, X)`, the source defines
  `d* = 1 + deg_Z(w_hat_0) + max_i deg_(X_i)(w_hat_0) = 3`; hence
  `d = max(d*, 3) = 3`.
- other symbols as in [protocol.md](protocol.md) and [verifier.md](verifier.md).

## Baseline

[Arnon, Chiesa, Fenzi, and Yogev, *WHIR: Reed–Solomon Proximity Testing with Super-Fast
Verification*](https://eprint.iacr.org/2024/1586). Construction 5.1 is the interactive
oracle proof of proximity for constrained Reed–Solomon codes that
`REQ-WHIR-VER-002..010` implement, and Theorem 5.2 gives its round-by-round soundness
errors. Construction 5.5 and Theorem 5.6 batch several constraints against one oracle;
they do not describe the production combination of several committed base oracles.
Sections 4.1 and 4.2 fix the proximity-generator and
list-decoding notions the theorem is conditioned on, and Conjecture 4.12 states the two
regimes in which mutual correlated agreement is assumed rather than proved. Section 6
evaluates three named configurations, WHIR-UD, WHIR-JB, and WHIR-CB, and it is the
source's own configuration section, not Construction 5.1, that introduces proof of work.

The relabeling between the source and this module is recorded in
[protocol.md](protocol.md): the source's `gamma_(i+1)`, `z_(i+1,0)`, `y_(i+1,0)`, and
`t_i` are this module's `gamma_i`, `z_(i+1)`, `y_(i+1)`, and `t_i`.

## Production deviations

Each row is a departure from the cited construction that the project adopts. A row is
not a finding; what a row leaves open is named in its last column.

| Deviation | Cited construction | Production form | Residual |
|---|---|---|---|
| proximity regime | three configurations, from unique decoding to capacity; WHIR-CB fixes `eta_i = r_i / 2` | `PessimisticConjectureMode` credits `rho_i` bits per query and adds 20% to the resulting query count, but fixes no `eta_i`, `delta_i`, or `list_(i,s)` | `ASM-WHIR-SND-001`; `GAP-WHIR-SND-001` |
| grinding inside the protocol | proof of work appears only in the source's configuration section, where it prices both proximity-gap and query errors | one nonce per round, positioned after the out-of-domain reply and before that round's query indices and `gamma_i` | `ASM-SEC-CRY-003`; `GAP-WHIR-SND-002` |
| out-of-domain samples | Construction 5.1 uses one per committed oracle; Section 6 permits repetition as required by the target | exactly one per committed oracle, independent of `m_i` and `list_(i,0)` | `GAP-WHIR-SND-002` |
| challenge field | one field `F` throughout the error terms | challenges and folded values in `E`, oracle values in `F`; on the L1 path `E = F` | `GAP-WHIR-SND-001` must justify scalar extension and use `|E|` in the imported bounds |
| domain schedule | any smooth `L_i` with order at least `2^(m_i)` | `L_i` of order `2^(m_i + rho_i)` from the selected set, at or below the field's two-adicity, so the rate improves every round instead of the domain halving | none |
| batching form | several constraints against one oracle | one random linear combination of `ell` base columns against one shared point, with the component columns committed across `2` or `3` Merkle trees before the challenge | `GAP-WHIR-SND-001` must prove the virtual-oracle reduction; multiple roots are a commitment layout, not an extra correlated-agreement claim |
| explicit tail | `Σ_i k_i ≤ m`, tail of `m − Σ_i k_i` variables | `Σ_i k_i ≤ m − 1` with the tail between `1` and `4` variables, and no committed oracle an encoding of a polynomial below `2^4` | none |
| challenge independence | each verifier message is a fresh uniform draw | words reduced modulo the characteristic with no rejection, and each round's `gamma_i` sharing a digest with that round's query indices | `GAP-TRANS-SND-005`; `DEV-TRANS-001` |
| final queries | direct equality of the folded oracle against the explicit polynomial | unchanged, and the only direct equality in the protocol | none |

No row removes a check the baseline requires, so this module records no `DEV`. The
overlapping-draw row is the transcript module's `DEV-TRANS-001` and is not restated
here.

## Assumptions

- **ASM-WHIR-SND-001 — Capacity-regime proximity generator.** When the capacity
  regime is selected, `Gen(l; alpha) = (1, alpha, …, alpha^(l-1))` has mutual
  correlated agreement for every round and folded code with the proximity bound and
  error form of Conjecture 4.12 item 2. The source proves this property only in the
  unique-decoding regime; its WHIR-CB parameterization additionally chooses
  `eta_i = r_i / 2` and constants `c1 = c2 = c3 = 1`. Those numerical choices are not
  implied by this assumption and are not fixed by the selected parameter sets.

## Error terms

Theorem 5.2, in this module's indexing, bounds the round-by-round errors below. Each is
a probability that one verifier message moves a doomed state to an undoomed one. Let
`CRS^(i,s)` denote the round-`i` code after `s` folds. Both the initial and later fold
coefficients are `3` because `d* = d = 3`.

- fold, round `i`, step `s`:
  `epsilon_fold_(i,s) ≤ 3 · list_(i,s-1) / |E| + err_cap(CRS^(i,s), 2, delta_i)`
- out of domain, oracle `f_i` for `i ∈ [1, M)`:
  `epsilon_out_i ≤ 2^(m_i) · list_(i,0)^2 / (2 · |E|)`
- shift into oracle `f_i` for `i ∈ [1, M)`:
  `epsilon_shift_i ≤ (1 − delta_(i-1))^(t_(i-1)) + list_(i,0) · (t_(i-1) + 1) / |E|`
- final queries:
  `epsilon_fin ≤ (1 − delta_(M-1))^(t_(M-1))`

Here `err_cap` is the capacity-regime proximity-generator error of Conjecture 4.12 item
2. It depends on the list size, `eta_i`, `r_i`, `|E|`, and conjectured constants.

The production handoff needs an additional project-derived virtual-oracle term. For
fixed component claims with a nonzero residual, combining `ell` components by powers
of uniform `gamma_whir` has collision probability at most `(ell − 1)/|E|`. This
root bound alone does not prove the required proximity/list statement for the combined
oracle, so the full term remains part of `GAP-WHIR-SND-001` and is owned here rather
than in GKR.

The selected scheduler instead computes

`t_i = ceil((6 / 5) · floor((lambda − pow_i) / rho_i))`

in `PessimisticConjectureMode`: it first credits `rho_i` bits per query, then adds a
20% query margin. This is not the theorem's query term. If
`delta_i = 1 − r_i − eta_i`, then

`(1 − delta_i)^(t_i) = (r_i + eta_i)^(t_i)`,

not `r_i^(t_i)`. Under the source's WHIR-CB choice `eta_i = r_i / 2`, the first round
of `REQ-PARAM-002` contributes only
`28 − 87 · log2(3/4) ≈ 64.1` query-plus-grinding bits, not 100. The 20% margin does not
close that difference.

Interpreting the scheduler's `rho_i` bits per query as `r_i^(t_i)` sets `eta_i = 0`.
That value is outside the positive-slack hypothesis of Conjecture 4.12 item 2, and its
capacity error and list bounds contain inverse powers of `eta_i`, so they diverge at
zero. Even ignoring that obstruction, the first-round rate `r_0 = 1/2` would require
`ceil((100 − 28)/log2(4/3)) = 174` queries under the WHIR-CB choice
`eta_0 = r_0/2`, not `87`.

`REQ-PARAM-008` conservatively substitutes the initial code's block length for a
virtual-oracle batching estimate. That estimate is not Theorem 5.6 instantiated for
production. No selected set assigns `eta_i` or the `list_(i,s)` family, so the fold,
out-of-domain, shift, final-query, and virtual-oracle terms cannot yet be evaluated. In
particular, the nonce after an out-of-domain reply does not price that reply.

## Open obligations

- **GAP-WHIR-SND-001 — Concrete theorem.** Instantiate the baseline analysis for every
  selected field, extension, hash, cap size, fold schedule, rate schedule, query
  schedule, proof-of-work value, and regime recorded in
  [parameters.md](../../soundness/parameters.md), and compose the per-round errors into
  a round-by-round bound for the whole opening proof. The instantiation must state the
  complete `list_(i,s)` family and every positive `eta_i` it uses; must prove the
  random-linear-combination reduction for the `ell` component columns, including
  scalar extension from `F` to `E`; must account for the two or three base-tree
  commitment layout at each round-0 query; and must account for `DEV-TRANS-001`,
  because a round's query indices
  and its `gamma_i` are not drawn from disjoint transcript words. The result populates
  `epsilon_whir` in [error-budget.md](../../soundness/error-budget.md).
- **GAP-WHIR-SND-002 — Unpriced round messages.** Decide whether the terms no
  proof-of-work stage prices reach the nominal level. Each round's nonce sits between
  the out-of-domain reply and that round's query indices, so it prices the indices and
  `gamma_i` but neither the out-of-domain point `z_(i+1)` nor any fold coordinate of
  `a_i`; `epsilon_out` and `epsilon_fold` therefore have to hold outright. The decision
  needs explicit list-size and positive-slack choices, the number of out-of-domain
  samples per round justified at `1`, and the scheduler's `rho_i`-bits-per-query
  heuristic replaced by or proved against the resulting theorem terms. If a term falls short, the remedy
  may require more queries or samples, a nonce before `z_(i+1)`, or a stated cost floor
  for regrinding a committed oracle.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-WHIR-SND-001` | normative | capacity-regime analysis | external boundary: proximity-generator conjecture; `GAP-WHIR-SND-001` | [WHIR, Conjecture 4.12 and the WHIR-CB configuration](https://eprint.iacr.org/2024/1586) |
| `GAP-WHIR-SND-001` | open | — | affects `REQ-WHIR-VER-002`, `REQ-WHIR-VER-005..010`, `OUT-WHIR-VER-001`, `OUT-BUDGET-001`; owner: human | no instantiated bound for any selected set |
| `GAP-WHIR-SND-002` | open | — | affects `REQ-WHIR-VER-004`, `REQ-PARAM-001..008`; owner: human | selected sets omit list-size and slack parameters; the query heuristic does not evaluate the theorem's query term, and no proof-of-work stage prices the out-of-domain point or fold coordinates |
