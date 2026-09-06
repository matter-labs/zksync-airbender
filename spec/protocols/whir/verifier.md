# WHIR-VER: WHIR verifier obligations

> Canonical acceptance obligations for the round schedule, oracle binding, query
> derivation and authentication, claim composition, and the final polynomial and
> weighted sum. Concrete fold, query, rate, and proof-of-work values are selected per
> profile and are not fixed here.

## Imports

- `protocols/whir/protocol.md`
- `protocols/sumcheck/verifier.md`
- `protocols/transcript/verifier.md`

## Guarantee

Under these obligations, acceptance implies that the batched claim supplied by
`OUT-GKR-VER-001` is consistent with the committed base oracles, up to the proximity,
out-of-domain, and query error left open by `GAP-WHIR-SND-001..002`.

## Inputs

- `F`, `E`, `m`, `M`, `k_i`, `m_i`, `rho_i`, `L_i`, `f_i`, `g_i`, `a_i`, `h_(i,l)`,
  `z_i`, `y_i`, `t_i`, `u_(i,j)`, `x_(i,j)`, `gamma_i`, `gamma_whir`, `pow_i`, `cap_i`,
  `c`, `z`, `P_n`, `ell`, `f_M`, `pow`, `eq`, `pack` — as defined in
  [protocol.md](protocol.md).
- `claim_i ∈ E` — the claim entering the Sumcheck steps of round `i`; `claim_0` is the
  GKR handoff claim.
- `claim_i' ∈ E` — the terminal Sumcheck claim of round `i`, exported by
  `OUT-SUM-VER-001`.
- `v_1, …, v_ell ∈ E` — the per-column base-oracle evaluation claims at `z`, exported by
  `OUT-GKR-VER-001`.
- `b_0, …, b_(2^(m_M) - 1) ∈ E` — the monomial coefficients of `f_M`.
- `bitrev_n(w)` — the `n`-bit reversal of `w`.

## Assumptions

- **ASM-WHIR-VER-001 — Batched initial claim.** GKR supplies `v_1, …, v_ell`, their
  common opening point `z`, the challenge `gamma_whir`, and every base-oracle cap, in
  memory, witness, setup column order, and draws `gamma_whir` only after the batching
  proof-of-work of `REQ-TRANS-VER-004`.
- **ASM-WHIR-VER-002 — Transcript causality.** Every coordinate, out-of-domain point,
  delinearization challenge, and query index is squeezed from a state that has absorbed
  the messages it binds, each nonce is verified at its scheduled state, and no challenge
  or index is prover-selected.
- **ASM-WHIR-VER-003 — Compiled schedule.** `M`, every `k_i`, `t_i`, `rho_i`, `pow_i`,
  the cap size `2^c`, the values per base leaf, and `pack` are the constants of the one
  parameter set the profile selects, exported by `OUT-PARAM-001`. A proof carries none
  of them, so no length or count in this module is prover-controlled.

## Canonical relation tree

> Interpret this tree under `ASM-WHIR-VER-001..003`. Navigation view only; leaf IDs name
> the canonical statements.

- **Before round `0`.**
  - **[`REQ-WHIR-VER-001`] Adopt the batched claim**
    `claim_0` and the message polynomial `f_0`, both formed by GKR, not re-formed here
- **Round `i ∈ [0, M − 1)`.**
  - **[`REQ-WHIR-VER-002`] Run the round's `k_i` Sumcheck steps**
    `REQ-SUM-VER-001..005` at `d = 2` with no equality prefactor, reducing `claim_i` to
    `claim_i'` at `a_i`
  - **[`REQ-WHIR-VER-003`] Absorb `cap_(i+1)` before any challenge that binds it**
  - **[`REQ-WHIR-VER-004`] Sample out of domain, then grind**
    draw `z_(i+1)`, absorb `y_(i+1)`, verify the `pow_i` nonce
  - **[`REQ-WHIR-VER-005`] Derive `t_i` query indices, then `gamma_i`**
  - **[`REQ-WHIR-VER-006`] Authenticate each queried leaf**
    - **`i = 0`** one leaf per base tree at the same index, against the base caps
    - **`i > 0`** one leaf against `cap_i`, never against `cap_(i+1)`
  - **[`REQ-WHIR-VER-008`] Fold each leaf and accumulate its weight**
  - **[`REQ-WHIR-VER-007`] Compose `claim_(i+1)`**
    from `claim_i'`, `y_(i+1)`, and the folded leaves
- **Round `M − 1`.**
  - **[`REQ-WHIR-VER-002`] Run the round's `k_(M-1)` Sumcheck steps**
  - **[`REQ-WHIR-VER-009`] Read `f_M`, grind, query, and check direct equality**
    absorb all `2^(m_M)` coefficients, verify the `pow_(M-1)` nonce, draw the final
    indices, authenticate against `cap_(M-1)`, and require each folded leaf to equal
    `f_M` at the query point
  - **[`REQ-WHIR-VER-010`] Check the accumulated weighted sum against `claim_(M-1)'`**
  - **[`OUT-WHIR-VER-001`] Export the discharged opening claim**

## Requirements

### REQ-WHIR-VER-001 — Initial claim and message polynomial

Take `claim_0` to be the batched claim of `REQ-GKR-VER-008`:

`claim_0 = Σ_(n=1)^(ell) gamma_whir^(n-1) · v_n`,

one power per committed base column, in memory, witness, setup column order. The
polynomial the rounds then test is the matching combination
`f_0 = Σ_(n=1)^(ell) gamma_whir^(n-1) · P_n`, so no oracle is committed for `f_0` and the
combination is formed at query-read time under `REQ-WHIR-VER-006`. WHIR neither
re-forms the claim nor re-draws `gamma_whir`.

The virtual-oracle reduction and its proximity error are owned by
`GAP-WHIR-SND-001` and budgeted at the `pow_batch` stage of `REQ-PARAM-008`, not by
any `pow_i`.

### REQ-WHIR-VER-002 — Scheduled rounds and folds

Execute all `M` rounds. Round `i` runs exactly `k_i` Sumcheck steps under
`REQ-SUM-VER-001..005` with `d = 2`, `eq_prefactor = 1`, and the summand
`eq(x, p) · f_i(x)`, reducing `claim_i` to `claim_i'` at `a_i`. A missing round, a
missing step, or a step count other than `k_i` is a rejection, not a shortened schedule;
the counts come from `ASM-WHIR-VER-003` and no proof field can change them.

Here the spec's `d = 2` means maximum univariate degree. The paper writes the same
constraint as membership in `F^{<3}[X]`, meaning degree strictly less than `3`.

Two schedule bounds are structural rather than parameter choices:

`Σ_(i=0)^(M-1) k_i ≤ m − 1`, so at least one variable always remains for `f_M`;

`k_0 = 1` below L1, because a base leaf holds exactly `2^(k_0)` values per column and
the base-oracle leaf width of `REQ-PARAM-001` fixes that width at `2`.

### REQ-WHIR-VER-003 — Oracle binding

Absorb `cap_(i+1)` before drawing any challenge that binds it:

`absorb(cap_(i+1)) → squeeze(z_(i+1)) → absorb(y_(i+1)) → grind(pow_i) → squeeze(u_(i,*)) → squeeze(gamma_i)`.

Cap words are absorbed raw and in ascending node then ascending word index under
`REQ-TRANS-VER-001`, `2^c` nodes per cap. A cap absorbed after any of these draws, or
omitted, is a rejection.

### REQ-WHIR-VER-004 — Out-of-domain reply and proof-of-work

Draw exactly one out-of-domain point `z_(i+1) ∈ E` per committed oracle, after
`cap_(i+1)` is absorbed, and read and absorb its reply `y_(i+1) ∈ E`. Then verify the
round's nonce under `REQ-TRANS-VER-005` and `REQ-TRANS-VER-011`, at the state that has
absorbed `y_(i+1)` and before any index of that round is drawn. A stage with `pow_i = 0`
still reads its two nonce words and still advances the state.

`y_(i+1)` is never accepted by an in-round equality. It enters the composition of
`REQ-WHIR-VER-007` and, as one accumulated constraint at `pow(z_(i+1), m_(i+1))`, the
final check of `REQ-WHIR-VER-010`.

The nonce is positioned between `y_(i+1)` and the indices, so it prices grinding on the
query indices and on `gamma_i` only. Neither `z_(i+1)` nor any coordinate of `a_i` is
drawn from a ground state, which is the subject of `GAP-WHIR-SND-002`.

### REQ-WHIR-VER-005 — Query derivation

Derive the round's indices from the transcript, never from the proof:

`u_(i,j) ← squeeze(state)`, `j ∈ [1, t_i]`.

Draw exactly `t_i` of them, each `m_i + rho_i - k_i` bits wide, taken sequentially from
the drawn word stream of `REQ-TRANS-VER-010` with the nonce-constrained word excluded
under `REQ-TRANS-VER-005`. There is no rejection sampling: an index is the masked low
bits of the stream, uniform only because `L_i^(2^k_i)` has power-of-two order. Repeated
indices within a round are admissible and reduce the effective query count. Draw
`gamma_i` only after the last index of the round. A prover-supplied index or challenge
is rejected under `REJ-TRANS-VER-002`.

### REQ-WHIR-VER-006 — Leaf authentication

Round `i` authenticates against the caps of the oracle it reads, never against the cap
it commits in the same round. For `i > 0` that is `cap_i`; for `i = 0` it is the base
caps of `ASM-WHIR-VER-001`, one leaf opened per base tree at the same index and combined
into `f_0` under `REQ-WHIR-VER-001`.

Hash the ordered leaf encoding from a fresh hash initialization vector, never from
transcript state. Below L1, the leaf is a word-string Blake2s hash and an internal node
is one final 16-word Blake2s block `left || right`, with eight words per child. On the
Proth120 L1 path, the leaf preimage is the concatenation of the 16-byte big-endian
canonical field elements and an internal node is `Keccak256(left || right)` over two
32-byte digests. Neither construction uses a transcript-state prefix or a domain tag.

At each path level, place the current digest on the left when the current index bit is
zero and on the right when it is one; place the sibling in the other position, hash the
pair, then shift the index right by one.

The leaf index is a function of the query index alone:

`leaf(u) = bitrev_(rho_i)(u mod 2^(rho_i)) · 2^(m_i - k_i) + ⌊u / 2^(rho_i)⌋`,

which is the identity when `rho_i = 0`. The path has `m_i + rho_i - k_i - c` levels;
after consuming them the residual index selects the cap node, and the recomputed digest
must equal that node in full. A leaf whose width, path length, or cap node differs from
these is a rejection.

### REQ-WHIR-VER-007 — Round claim composition

For `i ∈ [0, M − 1)`, compose the claim entering the next round:

`claim_(i+1) = claim_i' + gamma_i · y_(i+1) + Σ_(j=1)^(t_i) gamma_i^(j+1) · g_i(x_(i,j))`.

The powers of `gamma_i` start at `1` for the out-of-domain reply and continue at `j + 1`
for query `j`, so no two constraints of one round share a coefficient. `claim_i'` is the
value `OUT-SUM-VER-001` exports, with no equality prefactor applied.

### REQ-WHIR-VER-008 — Query fold and weight accumulation

Fold each authenticated leaf at the round's coordinates: the `2^(k_i)` leaf values
determine `g_i(x_(i,j))`. Base-oracle leaves are in evaluation form and are folded
with the domain twiddle. Intermediate and final leaves are in coefficient form in the
supported default build and are evaluated against the monomial tensor of `a_i`; they
use evaluation form only when the `eval_leaves` build feature is selected. This is a
round-class and build-configuration distinction, and the verifier must match the
committer.

Register each round-`i` constraint in the accumulated weight of
[protocol.md](protocol.md): the out-of-domain constraint at `pow(z_(i+1), m_(i+1))` with
coefficient `gamma_i`, and query `j` at `pow(x_(i,j), m_(i+1))` with coefficient
`gamma_i^(j+1)`, where `x_(i,j)` is the `2^(k_i)`-th power of the queried domain element.
Each later fold coordinate multiplies every registered constraint by the `eq` factor of
that coordinate and squares its point. The accumulated weight is discharged only by
`REQ-WHIR-VER-010`; no round requires a direct equality between a folded leaf and the
current claim.

### REQ-WHIR-VER-009 — Final polynomial and final queries

Read exactly

`2^(m_M) = 2^(m − Σ_i k_i)`

coefficients of `E` in ascending monomial order, absorb all of them, and only then
verify the final nonce and draw the final indices. The final round commits no cap, draws
no out-of-domain point, and draws no delinearization challenge.

Authenticate each final leaf against `cap_(M-1)` under `REQ-WHIR-VER-006`, fold it under
`REQ-WHIR-VER-008`, and require direct equality against `f_M`:

`Σ_(n=0)^(2^(m_M) - 1) b_n · x_(M-1,j)^n = g_(M-1)(x_(M-1,j))` for every `j ∈ [1, t_(M-1)]`.

The left side is `f_M(pow(x_(M-1,j), m_M))`, because a multilinear polynomial evaluated
at a `pow` point equals its monomial coefficient list evaluated at the generating scalar.
These are the only queries checked by direct equality; they are not accumulated into the
weight, and `f_M` receives no degree check beyond its fixed coefficient count.

### REQ-WHIR-VER-010 — Final weighted sum

Every accumulated constraint has the form `Z · eq(p, X)` with a coefficient in `E`.
Fixing the `Σ_i k_i` fold coordinates splits each `p` into a bound prefix and a tail of
`m_M` coordinates, so the sum of the accumulated weight over the hypercube is a linear
combination of evaluations of `f_M`. Reject unless

`Σ_e coeff_e · (Π_(l bound) eq(p_(e,l), a_l)) · f_M(tail(p_e)) = claim_(M-1)'`.

The constraints `e` are: the initial claim, with `p = z` and `coeff = 1`; one
out-of-domain constraint per committed oracle, with `p = pow(z_(i+1), m_(i+1))` and
`coeff = gamma_i`; and one constraint per query of every round but the last, with
`p = pow(x_(i,j), m_(i+1))` and `coeff = gamma_i^(j+1)`. Their number is

`1 + (M − 1) + Σ_(i=0)^(M-2) t_i`,

fixed by `ASM-WHIR-VER-003`. Completing every Sumcheck step, every Merkle path, and
every final equality is not sufficient for acceptance; this identity is the only place
the initial claim, the out-of-domain replies, and the non-final queries are discharged.

## Rejections

- **REJ-WHIR-VER-001 — Cap reuse.** Reject authentication of a round-`i` leaf against
  `cap_(i+1)` rather than the caps of `f_i`.
- **REJ-WHIR-VER-002 — Unchecked accumulation.** Reject a proof that satisfies every
  per-round Sumcheck relation, Merkle path, and final equality but fails
  `REQ-WHIR-VER-010`.
- **REJ-WHIR-VER-003 — Schedule substitution.** Reject a round count, fold width, query
  count, coefficient count, cap size, or leaf width other than the one
  `ASM-WHIR-VER-003` fixes, including a proof that supplies any of them.

## Outputs

- **OUT-WHIR-VER-001 — Discharged opening claim.** The statement that
  `f_0 = Σ_n gamma_whir^(n-1) · P_n` is within the proximity parameter of the code and
  agrees with `claim_0` at `z`, consumed by the enclosing verifier as the discharge of
  `OUT-GKR-VER-001` and quantified by [soundness.md](soundness.md).

## Open boundary

- The proximity parameter under which `t_i` is chosen, and the regime that justifies it,
  belong to [soundness.md](soundness.md) and to the selected parameter set.
- Whether the committed base columns are the columns of the compiled circuit is the
  concern of the GKR handoff and the generated verifier, not of this module.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-WHIR-VER-001` | normative | every WHIR invocation | discharged by `OUT-GKR-VER-001`, `REQ-GKR-VER-008`, `REQ-TRANS-VER-004`; `GAP-WHIR-SND-001` | project virtual-oracle batching; implementation of the supported configuration |
| `ASM-WHIR-VER-002` | normative | every challenge, index, and nonce | discharged by `OUT-TRANS-VER-001`, `REQ-TRANS-VER-002`, `REQ-TRANS-VER-005`; `DEV-TRANS-001` | Fiat-Shamir causality requirement |
| `ASM-WHIR-VER-003` | normative | every WHIR invocation | discharged by `OUT-PARAM-001` | implementation of the supported configuration |
| `REQ-WHIR-VER-001` | normative | every WHIR invocation | `ASM-WHIR-VER-001`; `REQ-GKR-VER-008`; `REQ-PARAM-008`; `GAP-WHIR-SND-001` | project virtual-oracle batching; implementation of the supported configuration |
| `REQ-WHIR-VER-002` | normative | every scheduled round | `ASM-WHIR-VER-003`; `REQ-SUM-VER-001..005`; `REQ-PARAM-001` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-003` | normative | every round that commits an oracle | `ASM-WHIR-VER-002`; `REQ-TRANS-VER-001..002` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586) |
| `REQ-WHIR-VER-004` | normative | every round that commits an oracle | `REQ-WHIR-VER-003`; `REQ-TRANS-VER-005`, `REQ-TRANS-VER-011`; `GAP-TRANS-SND-003`, `GAP-WHIR-SND-002` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-005` | normative | every round | `REQ-WHIR-VER-004`; `REQ-TRANS-VER-005`, `REQ-TRANS-VER-010`; `REJ-TRANS-VER-002`; `DEV-TRANS-001` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-006` | normative | every round | `REQ-WHIR-VER-003`, `REQ-WHIR-VER-005`; `ASM-SEC-CRY-002` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-007` | normative | every round that commits an oracle | `REQ-WHIR-VER-004`, `REQ-WHIR-VER-006`, `REQ-WHIR-VER-008`; `OUT-SUM-VER-001` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586) |
| `REQ-WHIR-VER-008` | normative | every query of every round | `REQ-WHIR-VER-005..006`; `REQ-PARAM-001`, `REQ-PARAM-007` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-009` | normative | the final round | `ASM-WHIR-VER-003`; `REQ-WHIR-VER-002`, `REQ-WHIR-VER-006`, `REQ-WHIR-VER-008` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586); implementation of the supported configuration |
| `REQ-WHIR-VER-010` | normative | the final round | `REQ-WHIR-VER-007..009` | [WHIR, Construction 5.1](https://eprint.iacr.org/2024/1586) |
| `REJ-WHIR-VER-001` | normative | every round | `REQ-WHIR-VER-006` | derived from `REQ-WHIR-VER-006` |
| `REJ-WHIR-VER-002` | normative | the final round | `REQ-WHIR-VER-010` | derived from `REQ-WHIR-VER-010` |
| `REJ-WHIR-VER-003` | normative | every WHIR invocation | `ASM-WHIR-VER-003`; `REQ-TRANS-VER-006..007` | derived from `ASM-WHIR-VER-003` |
| `OUT-WHIR-VER-001` | normative | accepted WHIR proof | `REQ-WHIR-VER-001..010`; `GAP-WHIR-SND-001..002` | derived from `REQ-WHIR-VER-010` |
