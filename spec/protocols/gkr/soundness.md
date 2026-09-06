# GKR-SND: GKR soundness

> The baselines the layered reduction claims lineage from, the production deviations
> that move Airbender away from them, the error terms those deviations make necessary,
> and the obligations that remain open.

## Imports

- `protocols/gkr/verifier.md`
- `protocols/sumcheck/soundness.md`

## Guarantee

Partial. The dimension-reducing layers of one lookup channel, taken alone, are the
construction of Papini and Haböck and carry that paper's bound as `REQ-GKR-SND-001`.
Nothing cited covers the generated circuit layers, the cached relations, the
uncommitted setup polynomials, the per-layer batching over compiled slot inventories,
or the per-column handoff as instantiated. This module names those obligations rather
than asserting a composed bound.

## Baseline

[Goldwasser, Kalai, and Rothblum, *Delegating Computation: Interactive Proofs for
Muggles*](https://www.microsoft.com/en-us/research/publication/delegating-computation-interactive-proofs-muggles/)
gives the lineage. [Thaler, *Proofs, Arguments, and Zero-Knowledge*, Section
4.6](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) is the closer
formulation: one Sumcheck per layer reduces a claim on the multilinear extension of
layer `i` to claims on layer `i + 1`; the two resulting claims are reduced to one; the
input-layer claim is checked directly; the soundness error is
`O(depth · log(size) / |F|)`. [Libra](https://eprint.iacr.org/2019/317) is a concrete
example in which GKR's terminal input-layer oracle access is instantiated by a
verifiable polynomial-delegation commitment. It supplies lineage for committing the
input layer, not a soundness theorem for Airbender's WHIR handoff.

[Papini and Haböck, *Improving logarithmic derivative lookups using
GKR*](https://eprint.iacr.org/2023/1284) is the baseline for the fraction trees: a
layered circuit over projective fraction pairs, the pair-combination layer
`(n, d) ← (n₀·d₁ + n₁·d₀, d₀·d₁)`, the per-layer combination of the numerator and
denominator claims by one challenge, the single-coordinate two-point reduction, and
the root identity `N = 0 ∧ D ≠ 0`.

[Dao and Thaler, *More Optimizations to Sum-Check
Proving*](https://eprint.iacr.org/2024/1210) records the prefactor form: for a
summand `eq(w, x) · p(x)` the prover may send a message of degree `d` rather than
`d + 1` and let the verifier reconstruct the missing equality factors. The production
reduction is the equivalent normalized form of `REQ-GKR-VER-010`, with the factor of
the bound coordinate carried in the message and the factor of the previous coordinate
applied by the verifier.

## Production deviations

Each item is a specification obligation, not an assessed defect.

| Deviation | Effect on the baseline argument |
|---|---|
| the layered object is the compiled constraint circuit with the lookup fraction trees and memory product trees built in, not a generic arithmetic circuit | the wiring predicate is a per-layer generated gate descriptor rather than an evaluable `add`/`mult` extension; `O(depth · log(size))` is not the operative count (`REQ-GKR-VER-003`) |
| generated gates include zero-output constraint gates, copy gates, materialization gates, and selector-masked padding gates | not all layer values are gate outputs; a constraint gate contributes a constant and consumes a batching slot (`REQ-GKR-VER-003`, `REQ-GKR-VER-007`) |
| many claims per layer are combined by successive powers of one challenge, over a compiled slot inventory | replaces the baseline's two-claim reduction with a batching term per layer (`REQ-GKR-SND-003`) |
| the two-point-to-one reduction is a single-coordinate interpolation, not a restriction to a line | matches Papini–Haböck, not Thaler; the prover sends two values per address instead of a degree-`k` univariate, and only dimension-reducing layers perform it (`REQ-GKR-VER-012`) |
| one digest supplies both `r_last` and `γ_l` at a dimension-reducing layer | the point coordinate and the batching challenge are distinct words of one transcript output; their joint uniformity is charged to `epsilon_fs`, not assumed here (`REQ-GKR-VER-007`) |
| the reduction stops at `2^e` explicit values per output polynomial, folded by an `eq` at a drawn top point | the baseline's claimed-output reduction is applied to a `2^e`-entry table rather than to the whole output layer (`REQ-GKR-VER-009`) |
| terminal channel checks are local computations on already-absorbed values | their position relative to the handoff draw carries no transcript consequence (`REQ-GKR-VER-005`) |
| cached relation values are supplied and recomputed from other claims of the same layer | introduces claim-level algebraic identities outside the gate model; the memory-tuple identity is what binds the exported products to the committed columns (`REQ-GKR-VER-011`) |
| uncommitted setup polynomials are evaluated from closed forms instead of opened | removes those columns from the commitment, and makes the closed forms part of the trusted relation (`REQ-GKR-VER-004`, `GAP-GKR-SND-002`) |
| the input layer is not evaluated by the verifier; its claims are batched per committed column and discharged by WHIR | replaces the baseline's direct input evaluation with a proximity argument (`REQ-GKR-VER-008`) |
| the merged and packed commitment modes change the cap set, and the packed mode merges runs of `2^pack` column claims under freshly drawn coordinates | the handoff is mode-dependent and the packed variant has no baseline (`GAP-GKR-SND-003`) |
| Fiat-Shamir with concrete hashes and two grinding stages | inherits `REQ-TRANS-VER-005` and `ASM-TRANS-SND-001` |

## Requirements

### REQ-GKR-SND-001 — Fraction-tree baseline error

For one lookup channel reduced by `h` pair-combination layers over an extension field
`E`, the cited bound is

`epsilon ≤ (2·(h − 1) + 1) / |E| + Σ_(j = e)^(k − 1) epsilon_sc(2^j)`,

with `epsilon_sc(2^j) ≤ 3·j / |E|` for a degree-three Sumcheck over `2^j` points,
giving

`epsilon ≤ (2h − 1 + 3h·(e + k − 1)/2) / |E|`.

Here `h = k − e` is the number of dimension-reducing layers, whose Sumcheck round
counts are `e, e + 1, …, k − 1`. The source field in the cited proposition is
instantiated as the production challenge field `E`. The bound covers the
per-layer numerator/denominator combination, the two-point reductions, and the
per-layer Sumchecks of one channel. It does not cover the circuit layers, the batching
of several channels into one layer reduction, or the root identity, which is
`REQ-LOOKUP-SND-002`.

### REQ-GKR-SND-002 — Prefactor neutrality

The prefactor form of `REQ-GKR-VER-010` moves one equality factor from the prover's
message to the verifier. The polynomial whose identity the round check tests is still
the degree-three reconstructed round polynomial, so the per-round polynomial-identity
term is unchanged at `3 / |E|` and no separate error is introduced. This is the
prefactor transformation of [Gruen, Section 3.2](https://eprint.iacr.org/2024/108);
[Dao and Thaler, Section 2.1](https://eprint.iacr.org/2024/1210) supplies the related
derive-one message economy.

The form is not optional: applying the accumulated product of already-fixed factors,
or omitting the factor entirely, changes the tested identity and is a different
protocol.

### REQ-GKR-SND-003 — Batching term inventory

For each layer close, a combination over `q_l` slots by successive powers of one
challenge contributes at most `(q_l − 1) / |E|` to `epsilon_gkr` before composition.
The virtual-oracle combination at the GKR-to-WHIR handoff is owned and charged by
WHIR, not counted again here.

The slot counts `q_l` are per-circuit constants of `IN-GKR-VER-001`; publishing them
is `GAP-BUDGET-001`.

## Open obligations

- **GAP-GKR-SND-001 — Adaptation theorem.** Relate every production deviation above
  to a baseline and compose its error with Sumcheck, the lookup argument, the
  global-product argument, and WHIR, over the per-circuit layer inventory. The result
  populates `epsilon_gkr` in [error-budget.md](../../soundness/error-budget.md).
- **GAP-GKR-SND-002 — Uncommitted setup closed forms.** Prove that each closed form
  of `REQ-GKR-VER-004` is the multilinear extension of the table `IN-LOOKUP-002`
  binds, for every supported trace log-size and word-bit width. An uncommitted
  column is admitted on the strength of its closed form alone, so a mismatch admits
  range queries against the wrong table with no other check to catch it.
- **GAP-GKR-SND-003 — Packed handoff accounting.** Account for the packed commitment
  mode of `IN-GKR-VER-002`: the extra drawn coordinates, the merge of `2^pack` column
  claims into one, the separate packing of the memory and setup runs, and the
  placement of the packing coordinates as the high coordinates of the opening point.
  No cited construction covers it, and it is the mode the L1 path uses.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `REQ-GKR-SND-001` | normative | dimension-reducing layers of one lookup channel | `REQ-GKR-VER-002`, `REQ-GKR-VER-012`; `GAP-SUM-SND-001` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284), Proposition 1 |
| `REQ-GKR-SND-002` | normative | every GKR Sumcheck round | `REQ-GKR-VER-010`; `GAP-SUM-SND-001` | [Gruen, Section 3.2](https://eprint.iacr.org/2024/108); [Dao and Thaler, Section 2.1](https://eprint.iacr.org/2024/1210) |
| `REQ-GKR-SND-003` | normative | every layer close | `REQ-GKR-VER-007`; `GAP-BUDGET-001` | Schwartz–Zippel bound on power-batched claims |
| `GAP-GKR-SND-001` | open | — | affects `REQ-GKR-VER-002..013`, `OUT-BUDGET-001`; owner: soundness | no adaptation theorem for the deviations above |
| `GAP-GKR-SND-002` | open | — | affects `REQ-GKR-VER-004`, `IN-LOOKUP-002`; owner: soundness | closed forms are trusted without a stated extension lemma |
| `GAP-GKR-SND-003` | open | — | affects `REQ-GKR-VER-008`, `OUT-GKR-VER-001`, `REQ-BUDGET-004`; owner: soundness | no baseline covers the packed commitment handoff |
