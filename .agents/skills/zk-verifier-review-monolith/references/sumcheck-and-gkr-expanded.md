# Expanded Sumcheck and GKR Verification

## What the verifier must enforce

### One sumcheck

The prover claims `S = Σ_{x ∈ {0,1}ⁿ} g(x)` for a multilinear-extension-based
`g` of known degree `d` in each variable. For round `k = 0..n-1`:

1. prover sends the univariate `pₖ(X)` of degree ≤ `d` (as `d+1` coefficients
   or `d+1` evaluations — know which, they are not interchangeable);
2. verifier checks `pₖ(0) + pₖ(1) == claimₖ`;
3. verifier absorbs `pₖ`, **then** draws `rₖ`;
4. `claimₖ₊₁ = pₖ(rₖ)`.

After the last round the verifier must check the final claim against `g`
evaluated at `(r₀,…,r_{n-1})` using values it can independently obtain — an
oracle opening, a committed evaluation, or a recursive claim.

Audit points, in order of yield:

- **The consistency check exists and is `pₖ(0)+pₖ(1) == claimₖ`**, not
  `pₖ(0) == claimₖ` or a check against the wrong round's claim.
- **The check happens before the absorb-and-draw**, or at least before the
  claim is used; and the absorb happens before the draw. All three orderings
  are independently wrong-able.
- **Degree bound.** The verifier must accept exactly `d+1` values. Accepting
  more coefficients silently raises the degree and breaks soundness; accepting
  fewer breaks completeness. `d` must match the actual gate degree — including
  the `+1` that the `eq` gating factor contributes.
- **Coefficient vs evaluation form.** If coefficients `c₀..c_d` are sent, then
  `p(0)=c₀` and `p(1)=Σcᵢ`; if evaluations at `0,1,2,…` are sent, the
  interpolation must be the matching one. A form mismatch between prover and
  verifier is a completeness break; a wrong reconstruction inside the verifier
  is a soundness break.
- **`claim₀`.** Where does the initial claim come from? It must be derived by
  the verifier from bound data, not read from the proof. If it is read, it must
  be checked against something.
- **The final check is not skipped.** A sumcheck that reduces a claim and then
  never grounds it proves nothing. Find where the final claim is discharged.

### The `eq` gating factor

Zero-checks are implemented as sumchecks against a random `eq(r, x)` weight, so
the round polynomial carries an extra degree and the verifier must track a
running `eq` prefactor across rounds. Audit:

- the prefactor is updated **every** round with the correct
  `(1-rₖ)(1-pₖ) + rₖpₖ` form for the round's point;
- it is applied on the correct side of the comparison, once, and not applied
  twice;
- the point `p` it is compared against is this layer's previous point, not a
  stale one;
- when the same sumcheck batches several relations, each has the gating it
  needs.

### Batching several claims into one sumcheck

Modern implementations avoid per-gate selectors by batching:
`eq·g₁ + α·eq·g₂ + α²·eq·g₃ + …`. Audit:

- **α is drawn after every `gᵢ`'s inputs are fixed** — that is, after the
  claims/evaluations being batched are absorbed;
- **powers are distinct and cover every term** — no repeated exponent, no term
  omitted from the accumulation, exponent order identical on both sides;
- **α ≠ 0 is not required but α with small multiplicative order is not
  exploitable** — confirm the batch is a polynomial identity in α of degree <
  |F|;
- **the batched claim is the batched combination of the individual claims**,
  with the same coefficients in the same order;
- the number of batched items is a constant or a bound parameter, not a
  prover choice.

Relations that must equal zero are folded in as gates whose value must be zero
and absorbed into the same batching. Confirm that a zero-relation's
contribution is genuinely `α^i · eq · g` and not `α^i · eq · (g - claimed)`
with a prover-supplied `claimed`.

## GKR layer structure

Layers run from outputs toward inputs. Each layer is a sumcheck reducing claims
about layer `i`'s outputs to claims about layer `i+1`'s outputs (or, at the
base, to claims about the committed base polynomials).

For each layer boundary, audit:

- **Claim carry.** The next layer's initial claim must be computed by the
  verifier from the previous layer's final evaluations and the batching
  challenge — not read from the proof and not carried from the wrong layer
  index.
- **Point carry.** The evaluation point handed to the next layer must be the
  folding challenges of this layer, in the right order, with the right length.
  Off-by-one in point length silently evaluates a different polynomial.
- **Folding direction.** LSB-first vs MSB-first folding must match between
  prover and verifier, and between the sumcheck round order and the `eq`
  polynomial construction and the query-index bit order in the PCS. A
  direction mismatch is often invisible in small tests.
- **Wiring / gate identity.** The verifier's per-layer accumulator must
  evaluate the *same* gate set the prover committed to, at the same addresses,
  in the same order. Where the verifier is generated from a circuit
  description, the audit target is the generated code, and the question is
  whether the generator can emit a layer whose gate set differs from the
  prover's for some circuit configuration.
- **Address deduplication and merging.** When several output claims share an
  address, or extra addresses are merged in, confirm the merge is a
  permutation-stable, deterministic order used identically on both sides, and
  that no claim is dropped.
- **New prover values introduced mid-protocol.** Cached/extra evaluations sent
  at a layer boundary must be (a) absorbed **in the same commit grouping the
  prover used**, (b) absorbed **before** the next batching challenge is drawn,
  and (c) themselves checked by a relation. Two separate absorbs of `A` then
  `B` are not the same transcript as one absorb of `A‖B` in a
  `H(seed ‖ data)`-per-call construction — verify the grouping, not just the
  contents.

## Dimension-reducing / early-terminated sumchecks

An optimization: stop the sumcheck while the polynomial still has `2^m`
values (m small, e.g. 8 or 16 elements) and send those values directly instead
of running to a single point. Audit:

- the number of remaining variables and the number of sent values are
  consistent and are compile-time or key-derived, not prover-chosen;
- the sent values are absorbed before the challenges that combine them;
- the claim is discharged as `Σ eq(challenges, i)·valueᵢ` over exactly the sent
  values, with `eq` built from the correct challenge subset in the correct bit
  order;
- the layer's remaining rounds count matches the point length used downstream.

## Multiple outputs and the final claims

The last GKR layer typically produces several claim pairs (lhs/rhs) — a
memory/permutation argument and one or more LogUp arguments. Audit:

- **each pair is extracted from the correct offsets** of the output evaluation
  vector, with the offsets derived from the same layout the prover used;
- **LogUp outputs are actually checked** by the verifier (the lhs/rhs
  consistency relation), not merely computed;
- **memory outputs are exported** as accumulators for the aggregation layer
  and not silently dropped for some circuit family;
- **no output group is skipped** when a circuit family lacks a component
  (`if num_x > 0` around an extraction is a transcript-shape conditional).

## Base-layer handoff to the PCS

The GKR reduction ends with claims about the committed base-layer polynomials
at one point. Audit:

- the point handed to the PCS is the full accumulated folding point, correct
  length, correct order;
- the batching challenge used to combine base-layer claims is drawn after all
  those claims are absorbed;
- every committed base polynomial appears in the batch exactly once with a
  distinct coefficient;
- the claims passed to the PCS are the ones the GKR check consumed, not a
  re-read copy.

## Soundness accounting

Record the error terms so the budget pass can use them:

- per sumcheck: `d·n / |F|` (degree × variables over field size);
- per batching challenge: (number of batched items) `/ |F|`, or the degree of
  the combination polynomial;
- per layer: sum over layers;
- the extension-field size, not the base-field size, is the relevant `|F|` —
  confirm challenges are actually drawn in the extension.

Then check the claimed security level against the total. See
`grinding-and-soundness-budget-expanded.md`.
