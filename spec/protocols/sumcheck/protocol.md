# SUM: Sumcheck construction

> The one-variable-per-round reduction of a Boolean-hypercube sum to one evaluation
> claim at a transcript-derived point, and the round message shapes of the two callers.
> Initial and final relations belong to the caller. This module carries no numbered
> claim; every enforceable statement is in [verifier.md](verifier.md).

## Imports

- `protocols/transcript/verifier.md`

## Guarantee

A completed reduction turns one claim about a sum over `{0, 1}^m` into one claim about a
single evaluation of the summand at a transcript-derived point of `E^m`, which the
caller then checks against its own relation.

## Symbols

- `E` — the field the coordinates, coefficients, and claims live in: the degree-four
  extension of the base field below L1, and the L1 field itself on the L1 path. Both
  have `log2 |E| > 122`.
- `m ∈ [1, ∞)` — the number of Sumcheck variables of one invocation, fixed by the
  caller. `j ∈ [1, m]` is the round index.
- `G` — the caller's summand as a function of the `m` summed variables, excluding any
  equality factor the reduction carries outside the round message. `G` is at most
  quadratic in each variable.
- `q = (q_1, …, q_m) ∈ E^m` — the point of the incoming claim, supplied by the caller.
- `a = (a_1, …, a_m) ∈ E^m` — the drawn coordinates; `a_j` is drawn in round `j`.
- `eq(y, z) = y · z + (1 − y)(1 − z)` — the single-coordinate equality factor. The
  `m`-coordinate factor is `Π_j eq(a_j, q_j)`.
- `s_j` — the round-`j` message polynomial in the variable bound by round `j`.
- `d` — the round-polynomial degree fixed by the caller: `d = 3` under GKR and `d = 2`
  under WHIR.
- `claim_j ∈ E` — the claim entering round `j`; `claim_1` is the caller's initial claim.
- `eq_prefactor_j ∈ E` — the scalar that round `j` applies to the Boolean sum of `s_j`.

## Round messages

Per round `j`, in this order:

1. The prover sends `s_j` as `d + 1` coefficients of `E` in ascending monomial degree.
2. The verifier checks the round relation of `REQ-SUM-VER-002` against `claim_j`.
3. The verifier absorbs all `d + 1` coefficients, then draws `a_j ∈ E`.
4. The claim and the equality prefactor advance per `REQ-SUM-VER-004`.

The verifier draws one coordinate per round and reconstructs nothing: every coefficient
of `s_j` is on the wire, including the one that step 2 already determines from
`claim_j`. After round `m` the caller reads its own final message — one at-point
evaluation per input polynomial under GKR, the authenticated leaves and plaintext
polynomial under WHIR — and checks the final relation of `REQ-SUM-VER-005`.

## Message shapes

| Caller | Sumcheck summand | `d` | Coefficients per round | Equality factor |
|---|---|---|---|---|
| GKR layer reduction | `eq(x, q) · G(x)` | 3 | 4 | `eq` of the current coordinate inside `s_j`; the one inherited factor carried as `eq_prefactor_j` |
| WHIR folding round | `eq(x, q) · f(x)`, `f` multilinear | 2 | 3 | every `eq` coordinate inside the summand; `eq_prefactor_j = 1` |

Under GKR, `s_j` carries the equality factor of its own coordinate but no earlier one,
so `claim_(j+1) = s_j(a_j)` carries exactly one factor, `eq(a_j, q_j)`. The next round
applies that same factor to its Boolean sum, so no equality factor accumulates. Under
WHIR the equality factors of bound coordinates stay folded into the coefficients of
`s_j`, so no prefactor is transmitted or carried.

## Data flow

```text
caller initial claim at point q
  → round j: d + 1 coefficients of s_j → absorb → draw a_j
  → claim_(j+1) ← s_j(a_j)
  → eq_prefactor_(j+1) ← eq(a_j, q_j)   [GKR only]
  → after round m: caller final message → caller final relation
```

Both callers reuse one round loop; only `d`, `m`, and the presence of the prefactor
differ. `m` is the log2 trace length for a compiled GKR circuit layer, a smaller
generated count for a dimension-reduction layer, and the scheduled fold width `k_i` of
`REQ-WHIR-VER-002` for WHIR round `i`.

## Open boundary

- The initial and final relations are not defined here. GKR supplies its gate relation
  and equality prefactor; WHIR supplies its scheduled fold relation and query carry.
- Batching several claims into one invocation happens before round 1 and is the
  caller's obligation.

## Metadata

- profile: all targets

This module states no identified claim. Its content is the reading map for
`REQ-SUM-VER-001..005` and `ASM-SUM-VER-001..002`.
