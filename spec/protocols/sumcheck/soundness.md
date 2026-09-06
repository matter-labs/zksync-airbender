# SUM-SND: Sumcheck soundness

> Baseline references for the reduction, the deviations the production form makes
> against them, the shape of the per-invocation error term, and the single open
> obligation: no concrete bound is instantiated at the assessed revision.

## Imports

- `protocols/sumcheck/verifier.md`
- `soundness/assumptions.md`

## Guarantee

None yet. The baseline soundness of the reduction is standard and the per-round
argument transfers to the production form, but no instantiation covers Airbender's
challenge distribution, per-invocation round counts, batching, and cross-invocation
challenge reuse together.

## Baseline

[Lund, Fortnow, Karloff, and Nisan, *Algebraic Methods for Interactive Proof
Systems*](https://doi.org/10.1145/146585.146605) is the lineage citation. Their stated
protocol reduces claims about matrix permanents, not sums over `{0, 1}^m`: the
hypercube formulation universally attributed to them is a later abstraction. The
per-round argument is already theirs — two distinct univariate polynomials of degree at
most `r` over a prime field agree on at most `r` points, so one drawn coordinate
collapses two claims into one with error at most `r` over the field size,
union-bounded over the rounds.

[Thaler, *Proofs, Arguments, and Zero-Knowledge*, Sections
4.1–4.2](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) is the
formulation this specification tracks: round polynomial in the variable being bound, the
round identity `s_(j-1)(a_(j-1)) = s_j(0) + s_j(1)`, a per-round degree check, and one
terminal evaluation of the summand at the drawn point. Proposition 4.1 gives perfect
completeness and soundness error at most `m · d / |F|` for a summand of degree at most
`d` in each variable; Section 4.2 sharpens the numerator to the sum of the per-variable
degrees. Section 4.6.7.1 is the source of the equality-polynomial form, where the
factor multiplies the whole summand and stays inside it.

Two further references cover the production form directly.
[Gruen, *Some Improvements for the PIOP for ZeroCheck*, Section
3](https://eprint.iacr.org/2024/108) and [Dao and Thaler, *More Optimizations to
Sum-Check Proving*](https://eprint.iacr.org/2024/1210) describe pulling equality factors
out of the round message; the latter also records the economy of sending `d` values and
letting the verifier derive the remaining one from the current claim. [Bagad, Domb, and
Thaler, *The Sum-Check Protocol over Fields of Small
Characteristic*](https://eprint.iacr.org/2024/1046) states the protocol with a
base-field summand and extension-field coordinates, which is Airbender's setting, and
its Theorem 1 gives soundness error at most `m · d / |E|` with `E` the field the
coordinates are drawn from, not the field the summand lives in.

## Production deviations

| Deviation | Baseline | Production form | Statement affected |
|---|---|---|---|
| equality factor partially removed from the round message | factor stays inside the summand | `s_j` keeps the current coordinate's factor and drops every earlier one; the verifier restores the single inherited scalar | `REQ-SUM-VER-002`; `REQ-SUM-VER-004` |
| monomial coefficients, none derived | `d + 1` evaluations, or `d` values under the derive-one economy | `d + 1` monomial coefficients, one of them determined by the round relation | `REQ-SUM-VER-001` |
| degree fixed by construction | verifier checks the degree of each received polynomial | `d` is a caller constant and the message length is structural | `REQ-SUM-VER-001`; `ASM-SUM-VER-001` |
| base-field summand, extension-field coordinates | one field throughout | tables over `F`, coordinates and claims over `E` | `REQ-SUM-VER-003` |
| non-uniform coordinates | uniform draw from the field | below L1 each coordinate is four 32-bit transcript words reduced modulo the base prime with no rejection sampling; at L1 it is one 16-byte lane reduced modulo the L1 prime | `REQ-SUM-VER-003`; `GAP-TRANS-SND-005` |
| batched and repeated invocations | one invocation, independent coordinates | many invocations over one transcript, each opened on a caller-batched claim, with the coordinate array of one invocation feeding the equality point of the next | `REQ-SUM-VER-002`; `REQ-SUM-VER-005` |
| degenerate prefactor | no analogue | a zero `eq_prefactor_j` leaves `s_j` unconstrained whenever `claim_j = 0` | `REQ-SUM-VER-002` |

None of these removes a check the baseline requires, so no `DEV` is recorded here. The
first two are wire-format and prover-work choices at fixed soundness; the rest change
the distribution or the composition the bound must be taken over.

## Error term

For one invocation of `m` rounds with round-polynomial degree `d`, under uniform
independent coordinates the baseline bound is

`epsilon ≤ m · d / |E|`.

Production coordinates are not uniform, so the bound has to be taken over the actual
distribution named by `ASM-SEC-ALG-002` and `GAP-TRANS-SND-005`. Below L1 each of the
four words of a coordinate is reduced modulo `p = 2^31 − 2^27 + 1` without rejection, so
a residue has two or three preimages among the `2^32` words and none is reached with
probability above `3 / 2^32`. Under `ASM-SEC-CRY-001`, treating the four words of one
draw as independent, no point of `E` is reached with probability above

`(3 / 2^32)^4 = (3 · p / 2^32)^4 / |E| < 3.92 / |E|`,

so each per-round application of the degree bound loses under two bits and

`epsilon ≤ 3.92 · m · d / |E|`.

With `log2 |E| ≥ 123` from `REQ-PARAM-008`, `d = 3` under GKR, and `d = 2` under WHIR,
any invocation with `m · d ≤ 2^8` satisfies `epsilon ≤ 2^(-113)`.

On the L1 path a coordinate is one 16-byte lane reduced modulo the L1 prime
`p = 7 · 2^120 + 1`, so each residue has `36` or `37` preimage lanes among the `2^128`
and no point is reached with probability above `37 / 2^128 = (37 · p / 2^128) / |E|`.
That factor is under `1.02`, so the loss there is under `0.03` bits: a wider lane
relative to the modulus makes the reduction nearly uniform.

Both derivations are conditional on the stated assumptions, not adopted bounds. Neither
covers the composition across invocations, the batching that forms each initial claim,
or the degenerate prefactor event, so neither closes `GAP-SUM-SND-001`.

## Open obligations

- **GAP-SUM-SND-001 — Concrete bound.** Instantiate the polynomial-identity bound for
  every GKR and WHIR Sumcheck invocation of a selected profile. The instantiation needs
  the per-invocation round count and degree, the actual coordinate distribution of
  `REQ-SUM-VER-003` rather than a uniform one, the batching that forms each initial
  claim, the reuse of one invocation's coordinates as the next invocation's equality
  point, the probability that `eq_prefactor_j = 0` at a zero claim, and the invocation
  inventory of `GAP-SOUND-001`. The result populates `epsilon_sum` in
  [error-budget.md](../../soundness/error-budget.md).

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `GAP-SUM-SND-001` | open | — | affects `REQ-SUM-VER-002`, `REQ-SUM-VER-003`, `REQ-SUM-VER-005`, `OUT-BUDGET-001`; owner: human | no instantiated bound over the production coordinate distribution and invocation graph |
