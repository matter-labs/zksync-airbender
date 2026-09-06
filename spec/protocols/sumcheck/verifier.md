# SUM-VER: Sumcheck verifier obligations

> The five obligations every Sumcheck invocation discharges, shared by the GKR layer
> reduction and the WHIR folding rounds. Callers import them and add only their own
> initial and final relations.

## Imports

- `protocols/sumcheck/protocol.md`
- `protocols/transcript/verifier.md`

## Guarantee

Under these obligations, acceptance of an invocation implies that the caller's initial
claim at `q` follows from the final evaluation claim at the drawn point `a`, up to the
polynomial-identity error left open by `GAP-SUM-SND-001`.

## Inputs

- `E`, `m`, `d`, `G`, `q`, `a`, `s_j`, `claim_j`, `eq` — as defined in
  [protocol.md](protocol.md).
- `c_(j,0), …, c_(j,d) ∈ E` — the coefficients of `s_j` read in round `j`, in ascending
  monomial degree, so `s_j(X) = Σ_(k=0)^d c_(j,k) · X^k`.
- `eq_prefactor_j ∈ E` — the scalar round `j` applies to the Boolean sum of `s_j`. It is
  the equality factor of the single most recently bound coordinate, not a product over
  bound coordinates; `eq_prefactor_1 = 1`.
- `x ∈ E^m` — the coordinate array the caller supplies and this module overwrites: on
  entry `x_j = q_j`; once round `j` completes, `x_j = a_j`.

## Assumptions

- **ASM-SUM-VER-001 — Summand degree.** For every invocation the caller's summand is at
  most quadratic in each summed variable, so the polynomial the honest prover must send
  has degree at most `d` and the fixed `d` of `REQ-SUM-VER-001` represents `s_j`
  exactly. A generated relation of higher per-variable degree is a completeness failure
  of the caller, not a widening of the round message.
- **ASM-SUM-VER-002 — Transcript causality.** Each `a_j` is squeezed from a state that
  has absorbed every earlier message including all of `s_j`, and no coordinate of `a` is
  prover-selected.

## Canonical relation tree

> Interpret this tree under `ASM-SUM-VER-001..002`. Navigation view only; leaf IDs name
> the canonical statements.

- **Round `j ∈ [1, m]`**
  - **[`REQ-SUM-VER-001`] Read the round message**
    Exactly `d + 1` coefficients of `E`, ascending degree, `d` fixed by the caller
  - **[`REQ-SUM-VER-002`] Check the round relation**
    - **Caller is WHIR**
      `eq_prefactor_j = 1`, so the Boolean sum alone must equal `claim_j`
    - **Caller is GKR**
      the Boolean sum scaled by `eq_prefactor_j` must equal `claim_j`
  - **[`REQ-SUM-VER-003`] Advance the transcript**
    Absorb all `d + 1` coefficients, then draw `a_j ∈ E`
  - **[`REQ-SUM-VER-004`] Advance the round state**
    `claim_(j+1)`, `eq_prefactor_(j+1)`, and `x_j`
- **After round `m`**
  - **[`REQ-SUM-VER-005`] Check the caller's final relation**
    against `claim_(m+1)` and `eq_prefactor_(m+1)`
  - **[`OUT-SUM-VER-001`] Export the reduced claim**
    the point `a` and the terminal claim

## Requirements

### REQ-SUM-VER-001 — Round message

Read exactly `d + 1` coefficients of `E` for round `j`, in ascending monomial degree:

`s_j(X) = Σ_(k=0)^d c_(j,k) · X^k`, with `d = 3` under GKR and `d = 2` under WHIR.

Each coefficient is one element of `E` read under `REQ-TRANS-VER-001`: four base-field
words below L1, so `16` words per GKR round message and `12` per WHIR round message, and
one `16`-byte lane on the L1 path under `REQ-TRANS-VER-012`. `d` is a protocol constant
of the caller, not a per-layer, per-round, or prover-supplied field. The message carries
no length; a message of the wrong length is rejected by the stream framing of
`REQ-TRANS-VER-006..007`.

The verifier reconstructs no coefficient. The coefficient that `REQ-SUM-VER-002`
determines from `claim_j` is transmitted redundantly, so one element of `E` per round is
wire overhead rather than a soundness input.

### REQ-SUM-VER-002 — Round relation

With `s_j(0) = c_(j,0)` and `s_j(1) = Σ_(k=0)^d c_(j,k)`, require

`(s_j(0) + s_j(1)) · eq_prefactor_j = claim_j`.

Under WHIR `eq_prefactor_j = 1` for every round, so this is the plain Boolean-sum
identity. Under GKR `eq_prefactor_1 = 1` and every later round uses the value assigned
by `REQ-SUM-VER-004`; the multiplication matches the single equality factor that
`claim_j` inherited, so both sides of the identity carry it.

When `eq_prefactor_j = 0` the relation determines `claim_j = 0` and constrains no
coefficient of `s_j`. That event is a named input of `GAP-SUM-SND-001`.

### REQ-SUM-VER-003 — Challenge order

Absorb every coefficient of `s_j` before drawing the round coordinate:

`absorb(c_(j,0) || … || c_(j,d)) → a_j ← squeeze(state)`.

`a_j` is one element of `E` produced by the challenge mapping of `REQ-TRANS-VER-010`
below L1 and of `REQ-TRANS-VER-012` on the L1 path, and is exported by
`OUT-TRANS-VER-001`. No round coordinate is drawn from the base field, no round
coordinate is prover-supplied, and because every draw follows the absorb of that round's
own message, no two rounds of one invocation draw the same transcript words.

### REQ-SUM-VER-004 — Round state update

Evaluate the transmitted coefficients at the drawn coordinate and advance:

`claim_(j+1) ← s_j(a_j)`

`eq_prefactor_(j+1) ← eq(a_j, q_j) = a_j · q_j + (1 − a_j)(1 − q_j)`

`x_j ← a_j`

Under WHIR the second assignment is absent: `eq_prefactor_j = 1` for every `j`. Under
GKR the prefactor is replaced, never multiplied into a running product: `s_j` already
excludes the equality factors of every coordinate bound before round `j`.

The coordinate pairing is positional. Round `j` reads `q_j` from position `j` of the
coordinate array and writes `a_j` back to the same position, so the array holds `q` for
positions not yet bound and `a` for positions already bound.

### REQ-SUM-VER-005 — Final relation

After round `m`, require the terminal claim to equal the caller's final relation at `a`.
A completed round loop without this check is not an accepted reduction.

Under GKR, require

`claim_(m+1) = G(a) · eq_prefactor_(m+1)`,

where `G(a)` is the layer gate relation of `REQ-GKR-VER-003` evaluated once from the
at-point evaluations read after round `m`, and `eq_prefactor_(m+1) = eq(a_m, q_m)`. Those
at-point evaluations are absorbed and are also the next layer's claims, so a single set
of values serves both this check and `REQ-GKR-VER-007`.

Under WHIR, `claim_(m+1)` enters the round composition of `REQ-WHIR-VER-007`, the query
carry of `REQ-WHIR-VER-008`, and the final weighted sum of `REQ-WHIR-VER-010`. Every
equality factor stays inside the summand, so no prefactor is applied.

## Outputs

- **OUT-SUM-VER-001 — Reduced evaluation claim.** The point `a`, the terminal claim
  `claim_(m+1)`, and `eq_prefactor_(m+1)`, consumed by `REQ-GKR-VER-003` and
  `REQ-WHIR-VER-007`.

## Open boundary

- Batching several claims into one invocation is the caller's obligation; see
  `REQ-GKR-VER-007` and `REQ-WHIR-VER-007`. This module states nothing about how many
  claims one invocation carries.
- Nothing here bounds `m`, the number of invocations, or the reuse of transcript state
  across invocations. Those are inputs to `GAP-SUM-SND-001`.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-SUM-VER-001` | normative | every Sumcheck invocation | `REQ-GKR-VER-003`; `REQ-WHIR-VER-002`; compiled-artifact boundary | compiled structural degree bound; [Thaler, Proposition 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) assumes, but does not authorize omitting, the verifier's degree check |
| `ASM-SUM-VER-002` | normative | every Sumcheck round | `REQ-TRANS-VER-002`; `REJ-TRANS-VER-002` | [Thaler, Section 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) |
| `REQ-SUM-VER-001` | normative | every Sumcheck round | `ASM-SUM-VER-001`; `REQ-TRANS-VER-001`; `REQ-TRANS-VER-006..007`; `REQ-TRANS-VER-012` | [Thaler, Section 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); implementation of the supported configuration |
| `REQ-SUM-VER-002` | normative | every Sumcheck round | `REQ-SUM-VER-001`; `REQ-SUM-VER-004` | [Thaler, Equation 4.6](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); equality-prefactor variant of the supported configuration |
| `REQ-SUM-VER-003` | normative | every Sumcheck round | `ASM-SUM-VER-002`; `REQ-TRANS-VER-010`; `REQ-TRANS-VER-012`; `OUT-TRANS-VER-001` | derived from `REQ-TRANS-VER-002` and the transcript challenge mapping |
| `REQ-SUM-VER-004` | normative | every Sumcheck round | `REQ-SUM-VER-001..003` | [Thaler, Section 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); [Gruen, Section 3](https://eprint.iacr.org/2024/108) as partially adapted by the supported configuration |
| `REQ-SUM-VER-005` | normative | after the last Sumcheck round | `REQ-SUM-VER-004`; `REQ-GKR-VER-003`; `REQ-WHIR-VER-007` | [Thaler, Section 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf); implementation of the supported configuration |
| `OUT-SUM-VER-001` | normative | completed reduction | `REQ-SUM-VER-001..005` | derived from `REQ-SUM-VER-004..005` |
