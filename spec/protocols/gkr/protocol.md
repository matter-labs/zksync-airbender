# GKR: Layered-circuit construction

> The compiled layer plan a verifier walks, what the prover sends for each layer class,
> what the verifier draws, and the point at which the base-layer claims are handed to
> WHIR. This module carries no numbered claims; the enforceable obligations are in
> [verifier.md](verifier.md).

## Imports

- `protocols/sumcheck/verifier.md`
- `protocols/transcript/verifier.md`

## Guarantee

Acceptance of the layer schedule reduces the explicit global output values of one
compiled circuit to one evaluation claim per committed base-layer column, all at one
transcript-derived point. The handoff combines those claims into the single opening
claim WHIR discharges.

## Symbols

- `F` — base field; `E` — its degree-four extension below L1, and `F` itself on the
  L1 path. Every claim, challenge, layer value, and output lives in `E`.
- `k` — trace log-size; a circuit layer carries `2^k` rows.
- `e` — explicit-output log-size: each output polynomial ends as `2^e` cleartext
  values. Supported circuits use `e = 4`, so `2^e = 16`.
- `c` — number of same-size circuit layers, indexed `l ∈ [0, c)`; layer `0` is the
  committed base layer.
- `L` — the walked layer sequence: dimension-reducing layers indexed
  `l ∈ [c, c + k − e)`, then circuit layers, taken in decreasing index order.
- `gate_l` — the generated gate relation of layer `l`, of degree at most two in that
  layer's input values.
- `p_l ∈ E^m` — the claim point entering layer `l`, of length `m` equal to that
  layer's round count.
- `eq1(a, b) = a·b + (1 − a)·(1 − b)` — the single-coordinate equality factor.
- `γ_l ∈ E` — the layer-`l` batching challenge.
- `r_last ∈ E` — the extra coordinate a dimension-reducing layer fixes outside its
  Sumcheck.
- `γ_whir ∈ E` — the WHIR batching challenge.
- `ℓ_mem`, `ℓ_wit`, `ℓ_set` — committed column counts of the memory, witness, and
  setup oracles; `ℓ = ℓ_mem + ℓ_wit + ℓ_set`.

## Layer classes

This is not GKR over a generic arithmetic circuit. The layered object is the compiled
constraint circuit with the lookup fraction trees and the memory product trees built
into it, so three layer classes exist and the verifier walks two of them.

| Class | Rows per layer | What one layer computes | Reduces |
|---|---|---|---|
| circuit layer | `2^k` | the generated gates of `gate_l`: materialization, copy, zero-check, lookup-pair, and product gates, each of degree at most two | tree width within one row |
| dimension-reducing layer | halves each layer | `v(y) ← v(2y) · v(2y + 1)` for a product channel; `(n, d) ← (n₀·d₁ + n₁·d₀, d₀·d₁)` for a lookup channel | one variable |
| explicit top | `2^e` | nothing; the remaining values are sent in cleartext | — |

The pairwise fraction sum is the projective addition of the logUp-GKR fraction tree: a
pair `(n, d)` denotes the fraction `n / d`, and combining two pairs preserves the sum
of the fractions they denote. The pairwise product is the ordinary grand-product tree.
Both are dimension-reducing, so one schedule reduces every channel in lockstep.

Circuit layers are all the same size. Width reduction inside a row and height
reduction across layers are therefore separate mechanisms: the circuit layers collapse
each channel to one polynomial, and the dimension-reducing layers collapse that
polynomial from `2^k` to `2^e` rows.

## Output channels

| Channel | Two polynomials | Terminal use |
|---|---|---|
| permutation product | read set, write set | exported products |
| 16-bit lookup | numerator, denominator | terminal rational identity |
| timestamp lookup | numerator, denominator | terminal rational identity |
| generic lookup | numerator, denominator | terminal rational identity |
| initialization/teardown product | read set, write set | exported products |

A circuit carries a subset of these channels. The order above is the order in which
the explicit values appear in the stream and the order of the batching slots at the
first walked layer. Every present channel contributes `2 · 2^e` explicit values.

## Messages

| Stage | Prover sends | Verifier draws |
|---|---|---|
| initialization | top bits; the cap of each present oracle class; the lookup-challenge nonce; then `2 · 2^e` values per present channel | the lookup challenges after the nonce; then `e + 1` elements of `E`: the `e` coordinates of the top point, then the first batching challenge |
| circuit layer (`k` rounds) | four coefficients per round polynomial; then one at-point evaluation per distinct input address, and one claimed value per cached relation | one coordinate per round; then, after one commit covering the evaluations and the cached values together, one element `γ_l` |
| dimension-reducing layer (`e + (c + k − e − 1 − l)` rounds) | four coefficients per round polynomial; then two values per input address, the layer polynomial at the two settings of the still-unbound low coordinate | one coordinate per round; then, from one digest, `r_last` followed by `γ_l` |
| handoff | the batching nonce | on the packed L1 path, the packing coordinates; after merging the claims and grinding the nonce, `γ_whir` |

Thus the packed handoff order is `packing coordinates → claim merge → batching
proof-of-work → γ_whir`.

Every round polynomial is cubic and is sent as four monomial coefficients: the gate
relation contributes a quadratic factor and the equality factor of the bound
coordinate contributes the third degree. The prover is free to derive one coefficient
from the running claim rather than accumulate it; the wire carries all four either way.

A circuit layer needs no extra coordinate because its last variable is bound by an
ordinary Sumcheck round. A dimension-reducing layer leaves the pairing coordinate
unbound inside its Sumcheck and fixes it in the open with `r_last`, which becomes the
new low coordinate of the next layer's claim point.

## Proof contents

A GKR proof carries the target's initialization image fields, the cap of each present
oracle class, the scheduled proof-of-work nonces, the explicit output values of every
present channel, the per-layer Sumcheck coefficients, per-layer final-step evaluations
and cached relation values, and the WHIR proof. Their order is the flattened order of
[transcript/protocol.md](../transcript/protocol.md). Below L1 the external challenges
are supplied by the enclosing verifier; the packed Proth120 L1 transcript derives them
after its initial commit.

## Data flow

```text
explicit output values per channel
  -> eq fold at the top point            (one claim per output polynomial)
  -> dimension-reduction layers          (one variable each, r_last per layer)
  -> compiled circuit layers             (gate relation per layer)
  -> one claim per committed base column
  -> WHIR
```

Each layer reduction applies the imported Sumcheck obligations. The claims a layer
produces are absorbed before the challenge that combines them is drawn, so the
combination at layer `l` binds every value it combines.

## Open boundary

- The generated gate relations themselves are circuit content, not protocol content;
  they belong to the compiled artifact and to the machine and argument modules that
  define what each column means.
- The closed forms of the uncommitted setup polynomials are stated as obligations in
  [verifier.md](verifier.md); that they extend the intended tables is
  `GAP-GKR-SND-002`.

## Metadata

- profile: all targets

This module states no identified claim. Its content is the reading map for
`REQ-GKR-VER-001..013`.
