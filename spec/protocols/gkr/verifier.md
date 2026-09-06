# GKR-VER: GKR verifier obligations

> Canonical acceptance obligations for the initialization image, the explicit-output
> reduction, the layer schedule, cached relation values, uncommitted setup
> polynomials, per-layer batching, the terminal channel checks, and the WHIR handoff.
> The lookup and global-product relations themselves are imported, not restated.

## Imports

- `protocols/gkr/protocol.md`
- `protocols/sumcheck/verifier.md`
- `protocols/transcript/verifier.md`
- `arguments/lookups/relation.md`
- `arguments/global-products/relation.md`

## Guarantee

Under these obligations, acceptance implies that every generated layer relation of the
selected compiled circuit holds at the drawn points, that every present lookup channel
satisfies its terminal rational identity, that the four exported multiset products are
the products of that circuit's emitted events, and that the claim entering WHIR is the
batched evaluation claim on that circuit's committed base columns at the drawn point.

## Symbols

- `F`, `E`, `k`, `e`, `c`, `L`, `gate_l`, `p_l`, `eq1`, `γ_l`, `r_last`, `γ_whir`,
  `ℓ_mem`, `ℓ_wit`, `ℓ_set`, `ℓ` — as defined in [protocol.md](protocol.md).
- `cap_setup`, `cap_memory`, `cap_witness` — the caps of the setup, memory, and
  witness oracles; only the caps of present classes exist.
- `x_C[i] ∈ E` for `i ∈ [0, 2^e)` — the explicit values of one polynomial of channel
  `C`. Named instances are `x_num`, `x_den` for a lookup channel and `x_read`,
  `x_write` for a product channel.
- `r_top ∈ E^e` — the top point at which the explicit values are folded.
- `v_0, …, v_(ℓ − 1) ∈ E` — the base-layer at-point claims, indexed in memory,
  witness, setup column order.
- `z ∈ E^k` — the base-layer opening point.
- `pack` — the packing log-width of the packed commitment mode; `0` in the unpacked
  modes.

## Inputs

- **IN-GKR-VER-001 — Compiled layer plan.** `k`, `e`, `c`, the per-layer round
  counts, gate descriptors, distinct-address lists, cached-relation descriptors,
  batching-slot inventory, output-channel map, and the base-layer column layout belong
  to one compiled circuit artifact and are constants of the verifier for that circuit.
  No part of the plan is read from the proof.

- **IN-GKR-VER-002 — Base oracle classes and commitment mode.** The committed base
  columns are partitioned into the memory, witness, and setup oracles of widths
  `ℓ_mem`, `ℓ_wit`, `ℓ_set`. One commitment mode is selected per target:

  | Mode | Caps | Column placement |
  |---|---|---|
  | separate | `cap_setup`, `cap_memory`, `cap_witness` | one oracle per class |
  | merged | `cap_setup`, `cap_memory` | witness columns follow the memory columns inside the memory oracle |
  | merged and packed | `cap_setup`, `cap_memory` | merged, and each run of `2^pack` consecutive columns shares one committed column position |

  A class of width zero has no cap, no columns, and no claims. The packed mode is the
  Proth120 L1 path; the recursion path uses the separate or merged mode.

- **IN-GKR-VER-003 — Explicit outputs.** Each present output channel supplies two
  polynomials of `2^e` values of `E`, in the channel order of
  [protocol.md](protocol.md). A channel absent from the artifact supplies nothing and
  its exported product is the multiplicative identity.

## Assumptions

- **ASM-GKR-VER-001 — Compiled schedule fidelity.** The layer inventory, gate
  relations, cached-relation descriptors, and base-layer column layout the verifier is
  generated from are those of the compiled circuit whose commitments it checks, and
  every committed column occupies exactly one base-layer position.
- **ASM-GKR-VER-002 — External challenge authenticity.** On an unpacked path, the
  lookup and permutation challenges supplied to this verifier are the transcript-derived
  ones the enclosing verifier recomputes and compares. The packed Proth120 L1 path
  derives them inside this transcript under `REQ-GKR-VER-001`.
- **ASM-GKR-VER-003 — Top-bit admission.** The initialization top bits are read from
  the stream and bound only by the initialization image. Their range and strict
  increase across instances are enforced by the enclosing full-statement verifier.

## Canonical relation tree

> Interpret under `ASM-GKR-VER-001..003`, `REQ-TRANS-VER-002`, and the imported lookup
> and global-product relations. Navigation view only; leaf IDs name the canonical
> statements.

- **Initialization.**
  - **[`REQ-GKR-VER-001`] Bind the initialization image**, grind the lookup nonce,
    draw the lookup challenges, then read and absorb the explicit outputs.
  - **[`REQ-GKR-VER-009`] Fold the explicit outputs** to one claim per output
    polynomial at `r_top`, and take the first batching challenge from the same draw.
- **Layer `l ∈ L`, in decreasing index order under [`REQ-GKR-VER-002`].**
  - **[`REQ-GKR-VER-003`] Reduce the layer** by Sumcheck with the prefactor of
    [`REQ-GKR-VER-010`], and check the gate relation at the drawn point.
  - **[`REQ-GKR-VER-007`] Close the layer:** absorb its final message, then draw.
    - **The layer is a dimension-reducing layer.** The message is two values per
      address; the draw yields `r_last` then `γ_l`; the claims are reduced under
      [`REQ-GKR-VER-012`].
    - **The layer is a circuit layer.** The message is one at-point evaluation per
      address together with every cached relation value, absorbed in one commit; the
      draw yields `γ_l`; the claims are those evaluations.
      - **The layer declares cached relation values.** Recompute and compare under
        [`REQ-GKR-VER-011`].
      - **The layer reads an uncommitted setup polynomial.** Recompute the closed
        form under [`REQ-GKR-VER-004`].
  - Combine the layer's claims into the next layer's initial claim with powers of
    `γ_l`, under [`REQ-GKR-VER-007`].
- **Terminal channel checks on the explicit outputs.**
  - **Lookup channel.** [`REQ-GKR-VER-005`].
  - **Product channel.** [`REQ-GKR-VER-006`], exported as [`OUT-GKR-VER-002`].
- **Handoff.** [`REQ-GKR-VER-013`] every committed column carries a base-layer claim;
  [`REQ-GKR-VER-008`] batch those claims and enter WHIR, exported as
  [`OUT-GKR-VER-001`].

## Requirements

### REQ-GKR-VER-001 — Initialization image

Initialize one target-specific contiguous image:

- below L1:
  `top bits || external challenges || cap_setup || cap_memory || cap_witness`;
- packed Proth120 L1:
  `register final state || final PC and timestamp || top bits || cap_setup || cap_memory`,
  where the register state is 32 triples `(value, timestamp_lo, timestamp_hi)` and the
  following triple is `(final_pc, final_timestamp_lo, final_timestamp_hi)`.

Only caps of present oracle classes appear. The image is one stateless commit under
`REQ-TRANS-VER-009`. Below L1, the external challenges are supplied by the enclosing
verifier and are not read from the stream. On the packed Proth120 L1 path, after the
initial commit and the combined external/lookup grinding stage, draw nine elements:
seven global-product challenges followed by lookup `α` and `β`.

The explicit outputs of `IN-GKR-VER-003` are absorbed after the lookup-challenge
proof-of-work and the lookup challenges of `REQ-TRANS-VER-003`, and before any layer
reduction.

### REQ-GKR-VER-002 — Layer schedule

Verify `k − e` dimension-reducing layers and `c` circuit layers, in decreasing index
order: indices `c + k − e − 1` down to `c`, then `c − 1` down to `0`. A circuit layer
runs `k` Sumcheck rounds; the dimension-reducing layer of index `l` runs
`e + (c + k − e − 1 − l)` rounds and fixes one further coordinate under
`REQ-GKR-VER-012`.

Every count, index, and address list is a constant of `IN-GKR-VER-001`. The stream
carries no layer count, no layer index, and no address list. Each component therefore
reads the fixed prefix its compiled schedule requires; underflow fails where the input
source can signal it.

### REQ-GKR-VER-003 — Layer relation

For each layer `l`, apply `REQ-SUM-VER-001..005` with four coefficients per round
polynomial, and supply as the final relation of `REQ-SUM-VER-005` the generated gate
relation of that layer:

`claim_(m + 1) = gate_l(input evaluations at the drawn point) · eq1(r_m, p_l[m])`,

where `m` is the layer's round count and `r_m` the last drawn coordinate. The gate
relation is evaluated once, at the single point the reduction reached; no per-endpoint
evaluation is admissible.

A gate that enforces a constraint rather than producing a value contributes the
constant `0` at its position in the relation, so its value is not prover-supplied.

### REQ-GKR-VER-004 — Uncommitted setup polynomials

Recompute and compare every uncommitted setup evaluation the base layer reads,
evaluating the closed form at the folding point `pt ∈ E^k` in ascending coordinate
order.

A range channel of width `b` bits is the zero-padded ramp
`[0, 1, …, 2^b − 1, 0, …, 0]` of length `2^k`, whose multilinear extension is

`(Σ_(j = 0)^(b − 1) 2^j · pt[j]) · (Π_(j = b)^(k − 1) (1 − pt[j]))`,

with `b = 16` for the 16-bit channel and `b = 19` for the timestamp channel. For a
word-bit width `w`, with `t = 16 − w`, the two initialization/teardown address
polynomials evaluate to

`Σ_(j = 0)^(t − 1) 2^(w + j) · pt[j]` and `Σ_(j = 0)^(k − t − 1) 2^j · pt[t + j]`.

An uncommitted setup column is not committed and is never opened, so its claimed
evaluation is admissible only when the verifier derives it from the closed form. That
each closed form extends the table `IN-LOOKUP-002` declares is `GAP-GKR-SND-002`.

### REQ-GKR-VER-005 — Lookup outputs

For each present lookup channel, accumulate the `2^e` explicit pairs
`(x_num[i], x_den[i])` by the pair accumulation of `REQ-LOOKUP-VER-003` and accept the
channel only under the terminal identity of `REQ-LOOKUP-VER-004`:

`N = 0 ∧ D ≠ 0`.

Apply the check independently per channel under `REQ-LOOKUP-VER-005`. This is the
proof-level completion that `ASM-LOOKUP-002` names. `REQ-GKR-VER-001` discharges the
challenge binding of `REQ-LOOKUP-VER-001`; this requirement discharges the pair
reduction and per-instance terminal checks of `REQ-LOOKUP-VER-002..005`.

The check consumes only values already absorbed under `REQ-GKR-VER-001` and draws no
challenge, so comparison may occur after the handoff draw of `REQ-GKR-VER-008` without
changing what that draw binds.

### REQ-GKR-VER-006 — Global outputs

For each present product channel, form the two products over its explicit values:

`P_read = Π_(i = 0)^(2^e − 1) x_read[i]`

`P_write = Π_(i = 0)^(2^e − 1) x_write[i]`.

Apply this to the permutation channel and to the initialization/teardown channel
separately, yielding four elements of `E`. This module compares nothing: the four
products are exported as `OUT-GKR-VER-002` and the aggregate equality is
`REQ-GP-VER-005`. An absent channel exports the multiplicative identity.

An output index not named by the artifact is unreachable, not ignored.

### REQ-GKR-VER-007 — Layer close and batching

Absorb the layer's produced claims before drawing the challenge that combines them.

For a circuit layer, the at-point evaluations and the cached relation values of
`REQ-GKR-VER-011` are absorbed together in one commit, then one element `γ_l` is
drawn. For a dimension-reducing layer, the two-point lines are absorbed in one commit,
then one digest supplies two elements: `r_last` first, then `γ_l`.

Combine the next layer's claims in the generated slot order with successive powers:

`claim_(l − 1) ← Σ_i γ_l^i · v_i`, powers starting at `γ_l^0 = 1`.

The slot inventory is a constant of `IN-GKR-VER-001`, and a slot that carries no
prover-supplied claim still consumes its power, so the exponent of a claim is fixed by
the compiled plan and not by the proof. A fresh `γ_l` is drawn per layer; no batching
challenge is reused across layers.

### REQ-GKR-VER-008 — WHIR handoff

On the packed path, first draw the `pack` packing coordinates and merge each run of
`2^pack` consecutive base-column claims by multilinear evaluation in those
coordinates. Then, on every path, perform the batching proof-of-work of
`REQ-TRANS-VER-004`, draw `γ_whir`, and batch the resulting base-column claims with
successive powers:

`claim_whir ← Σ_(i = 0)^(ℓ − 1) γ_whir^i · v_i`.

The index `i` runs over committed columns, not oracle classes, in memory, witness,
setup column order; a class of width zero contributes no term. On the packed path the
packing coordinates extend the opening point as its high coordinates, and the memory
and setup runs are packed separately.

Supply `claim_whir`, the per-column claims it was formed from, the opening point `z`,
and every present cap class to the WHIR verifier.

The column order above differs from the setup, memory, witness cap order of
`REQ-GKR-VER-001`. Both orders are part of the contract and neither may be substituted
for the other.

### REQ-GKR-VER-009 — Explicit-output reduction

After absorbing the explicit outputs, draw `e + 1` elements of `E`: the `e`
coordinates of `r_top`, then the first batching challenge. Reduce each output
polynomial of each present channel to one claim by its multilinear extension at
`r_top`:

`claim_C ← Σ_(i = 0)^(2^e − 1) eq(r_top, bits_e(i)) · x_C[i]`,

where `bits_e(i)` is the `e`-bit Boolean vector of the index `i` and `eq` is the
multivariate equality polynomial.

`r_top` is the initial claim point of the first walked layer, and the first batching
challenge combines these claims under `REQ-GKR-VER-007`. Both are drawn after the
values they bind, so no explicit output may be chosen with knowledge of `r_top`.

The same absorbed values are consumed unfolded by `REQ-GKR-VER-005` and
`REQ-GKR-VER-006`; the fold does not replace those checks.

### REQ-GKR-VER-010 — Equality prefactor

Every GKR round polynomial carries the equality factor of the coordinate it binds, so
the prefactor the verifier applies is one single-coordinate factor, not a running
product. In round `j` of the reduction of layer `l`:

`(s_j(0) + s_j(1)) · eq1(r_(j − 1), p_l[j − 1]) = claim_j`,

with the prefactor `1` in the first round, and the terminal relation of
`REQ-GKR-VER-003` applying `eq1(r_m, p_l[m])`. This is the `eq_prefactor` of
`REQ-SUM-VER-002` and `REQ-SUM-VER-005` for GKR callers.

Applying the accumulated product of the already-fixed factors instead would reject
honest proofs: each factor is discharged exactly once, in the round after the
coordinate it belongs to is drawn.

### REQ-GKR-VER-011 — Cached relation values

Recompute every declared cached relation value from the layer's other claims and
compare it with the supplied value. The declared classes are the single-column lookup
input, the vectorized lookup input, the vectorized lookup setup, and the memory
tuple. A supplied cached value is never accepted unrecomputed.

All supplied values are absorbed before `γ_l` is drawn. The deterministic
recomputation and comparison may execute after that draw because neither depends on
`γ_l`; this does not alter transcript causality.

The memory-tuple recomputation is load-bearing: the product gates treat a memory tuple
as an opaque input, so without it the exported products of `REQ-GKR-VER-006` are not
bound to the committed memory columns and `REQ-GP-REL-001` is not enforced for this
proof.

### REQ-GKR-VER-012 — Two-point-to-one reduction

A dimension-reducing layer leaves the pairing coordinate unbound inside its Sumcheck.
For each input address the prover supplies the layer polynomial at the two settings of
that coordinate, and the verifier reduces the two claims to one by multilinear
interpolation at the `r_last` of `REQ-GKR-VER-007`:

`v ← (1 − r_last) · v[0] + r_last · v[1]`.

`r_last` becomes the low coordinate of the next layer's claim point, so the point
grows by one coordinate per dimension-reducing layer, from `e` after
`REQ-GKR-VER-009` to `k` at the base layer. A circuit layer performs no such
reduction: its final message is one at-point evaluation per address and the next
claim is that value.

### REQ-GKR-VER-013 — Base-layer coverage

Every committed base column of `IN-GKR-VER-002` occupies exactly one base-layer claim
position, and the claims exported by `REQ-GKR-VER-008` cover all `ℓ` of them. A
committed column with no base-layer claim would be committed but unconstrained; a
claim position with no committed column would batch a value WHIR does not open. This
is a construction obligation on the generated verifier, discharged by
`ASM-GKR-VER-001`, not a runtime comparison.

## Rejections

- **REJ-GKR-VER-001 — Unrecomputed derived value.** Acceptance is impossible when a
  cached relation value or an uncommitted setup evaluation is taken from the proof
  without the recomputation of `REQ-GKR-VER-011` or `REQ-GKR-VER-004`.
- **REJ-GKR-VER-002 — Vanishing lookup denominator.** A channel whose terminal
  denominator is zero rejects under `REQ-GKR-VER-005`, whatever its numerator.

## Outputs

- **OUT-GKR-VER-001 — Batched opening claim.** `claim_whir`, the per-column claims it
  was formed from, the opening point `z`, and the present cap classes, consumed by
  `REQ-WHIR-VER-001`.
- **OUT-GKR-VER-002 — Per-proof multiset products.** The four products of
  `REQ-GKR-VER-006`, established as the products of this circuit's emitted events
  under the supplied challenge vector. This discharges `ASM-GP-VER-001` for this
  proof and is consumed by `REQ-GP-VER-001`.

## Open boundary

- Whether the compiled circuit itself faithfully expresses the machine and argument
  relations is a property of the compiler and its input artifact, not of this module;
  `ASM-GKR-VER-001` states the boundary.
- The base-layer claims of committed columns are not checked here. Their soundness
  rests entirely on the WHIR opening of `OUT-GKR-VER-001`.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `IN-GKR-VER-001` | normative | construction | — | compiled layer plan of the supported configuration |
| `IN-GKR-VER-002` | normative | construction | `IN-GKR-VER-001` | base commitment modes of the supported configurations |
| `IN-GKR-VER-003` | normative | construction | `IN-GKR-VER-001` | compiled output-channel map |
| `ASM-GKR-VER-001` | normative | every GKR proof | external boundary: circuit compiler and verifier generator | compiled artifact is the generator's input |
| `ASM-GKR-VER-002` | normative | unpacked GKR proof | `REQ-GP-VER-003`, `REQ-LOOKUP-VER-001` | external challenges recomputed by the enclosing verifier |
| `ASM-GKR-VER-003` | normative | circuit carrying an initialization window | external boundary: full-statement verifier; `REQ-FSV-UNI-005` | top bits bound by the initialization image only |
| `REQ-GKR-VER-001` | normative | every GKR proof | `IN-GKR-VER-002`; `REQ-TRANS-VER-001..003`, `REQ-TRANS-VER-009` | implementation of the supported configuration |
| `REQ-GKR-VER-002` | normative | every GKR proof | `IN-GKR-VER-001`; `REQ-TRANS-VER-006..007` | implementation of the supported configuration |
| `REQ-GKR-VER-003` | normative | every walked layer | `REQ-SUM-VER-001..005`; `REQ-GKR-VER-002`, `REQ-GKR-VER-010` | [Thaler, Proofs, Arguments, and Zero-Knowledge, Section 4.6](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); generated gate relations |
| `REQ-GKR-VER-004` | normative | base layer reads an uncommitted setup column | `IN-LOOKUP-002`, `REQ-LOOKUP-VER-001`; `GAP-GKR-SND-002` | implementation of the supported configuration |
| `REQ-GKR-VER-005` | normative | every present lookup channel | `REQ-LOOKUP-VER-002..005`; challenge binding by `REQ-GKR-VER-001` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284); root identity of the fraction tree |
| `REQ-GKR-VER-006` | normative | every present product channel | `REQ-GP-REL-002`; `REQ-GKR-VER-001`, `REQ-GKR-VER-011` | implementation of the supported configuration |
| `REQ-GKR-VER-007` | normative | every walked layer | `IN-GKR-VER-001`; `REQ-TRANS-VER-002`, `REQ-TRANS-VER-010`; `REQ-GKR-VER-003` | implementation of the supported configuration |
| `REQ-GKR-VER-008` | normative | end of the layer schedule | `IN-GKR-VER-002`; `REQ-TRANS-VER-004`; `REQ-GKR-VER-007`, `REQ-GKR-VER-013` | implementation of the supported configuration |
| `REQ-GKR-VER-009` | normative | every GKR proof | `IN-GKR-VER-003`; `REQ-TRANS-VER-002`; `REQ-GKR-VER-001` | [Thaler, Proofs, Arguments, and Zero-Knowledge, Section 4.6](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); claimed-output reduction |
| `REQ-GKR-VER-010` | normative | every GKR Sumcheck round | `REQ-SUM-VER-002`, `REQ-SUM-VER-005` | [Dao and Thaler, eprint 2024/1210](https://eprint.iacr.org/2024/1210); Gruen prefactor form as implemented |
| `REQ-GKR-VER-011` | normative | layer declares a cached relation | `REQ-GP-REL-001`, `REQ-LOOKUP-006`; `REQ-GKR-VER-007` | implementation of the supported configuration |
| `REQ-GKR-VER-012` | normative | every dimension-reducing layer | `REQ-GKR-VER-007` | [Papini and Haböck, eprint 2023/1284](https://eprint.iacr.org/2023/1284); single-coordinate two-point reduction |
| `REQ-GKR-VER-013` | normative | construction | `IN-GKR-VER-002`; `ASM-GKR-VER-001` | base-layer column layout of the supported configuration |
| `REJ-GKR-VER-001` | normative | derived value present | derived from `REQ-GKR-VER-004`, `REQ-GKR-VER-011` | derived from `REQ-GKR-VER-004` and `REQ-GKR-VER-011` |
| `REJ-GKR-VER-002` | normative | every present lookup channel | derived from `REQ-GKR-VER-005` | derived from `REQ-LOOKUP-VER-004` |
| `OUT-GKR-VER-001` | normative | accepted layer schedule | `REQ-GKR-VER-008` | derived from `REQ-GKR-VER-008` |
| `OUT-GKR-VER-002` | normative | accepted layer schedule | `REQ-GKR-VER-006`, `REQ-GKR-VER-011`; discharges `ASM-GP-VER-001` | derived from `REQ-GKR-VER-006` and `REQ-GKR-VER-011` |
