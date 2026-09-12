# Expanded PCS Verification — WHIR / FRI-style

WHIR is the multilinear (MLE) analogue of FRI used to open the committed base
layer after a GKR reduction. The audit structure below applies to both; FRI-
specific and STARK-era notes are in `stark-deep-fri.md`.

## What the PCS verifier must enforce

An accepting run must establish: the committed oracle is close to a codeword of
the claimed degree/dimension, **and** that codeword's multilinear extension
evaluates to the claimed value at the claimed point.

Both halves matter. A proximity check with no evaluation binding proves the
prover committed to *some* low-degree thing, not to the polynomial whose
evaluation the GKR phase consumed.

## Round structure and the audit points

Per round, the typical schedule is:

```text
absorb  oracle commitment (root or cap)
draw    out-of-domain (OOD) point(s)
absorb  claimed OOD evaluation(s)
grind   proof of work
draw    delinearization / batching challenge
        [sumcheck rounds: absorb round poly → draw folding challenge]
draw    query indices
absorb/verify  query openings + Merkle paths
```

Audit each arrow:

### Commitments

- The commitment is absorbed **before** any challenge that must bind it —
  especially before the OOD point and before the query indices.
- Cap-based trees: the whole cap is absorbed, not just its first digest. Cap
  size is a fixed parameter, not read from the proof.
- The final-round oracle (often sent in the clear as coefficients/monomials) is
  absorbed before the final grinding and final queries.
- Where a commitment must equal a setup/preprocessed value, the comparison is
  done and covers every word.

### Out-of-domain samples

The OOD sample is what ties the folded oracle to a specific polynomial and
prevents the prover from choosing a different nearby codeword.

- The OOD point is **drawn**, never read.
- The claimed OOD evaluation is **absorbed after** the point is drawn — reading
  the evaluation first would let the prover pick a point that matches.
- The OOD evaluation participates in the next round's consistency check; an
  absorbed-but-unused OOD value is a missing check.
- Sampling from the evaluation domain instead of outside it voids the argument;
  confirm the domain-exclusion property holds by construction (extension field)
  or by check.

### Folding

- The folding challenge is drawn after the round's commitment and OOD data are
  absorbed.
- The folding arity (2, 4, 8, …) and schedule are fixed parameters and identical
  on both sides.
- The verifier's fold of the queried leaf values must reproduce exactly the
  prover's fold: same coset ordering, same generator powers, same bit-reversal
  convention. Bit-reversal and coset-ordering mismatches are the classic silent
  FRI/WHIR bug — they are invisible for arity 2 with symmetric data and appear
  only for specific index patterns.
- The folded claim carried into the next round is computed by the verifier, not
  read.

### Query derivation

- Indices are **drawn from the transcript after** the round's commitment, OOD
  data, and grinding.
- The number of bits drawn per index equals the log of the domain size for that
  round; check the round-dependent domain shrinkage is applied.
- Any convention that skips leading words of the drawn stream (for example
  because a grinding step consumed one) must match the prover exactly — a
  one-word offset yields a completely different, prover-predictable index set
  only if the prover knows the convention, which it does.
- Bits→index assembly: endianness, masking, and whether the same bit stream is
  consumed for successive indices without overlap.
- Duplicate indices reduce the effective query count. Determine whether the
  soundness claim assumes distinct queries; if it does, either the code must
  enforce distinctness or the budget must account for collisions.
- The index count equals the parameter for the claimed security level and is
  not read from the proof.

### Merkle / opening verification

- Every queried position is verified against a bound root or cap. Count them:
  `queries × oracles × rounds` openings expected, and that many verified.
- The path length matches the tree depth for that round's domain.
- The leaf index used for the path traversal is derived from the query index by
  the same transform as the leaf's position in the data (coset mapping,
  bit-reversal, tree layout). A path that verifies against the *wrong* leaf
  position is a silent break.
- The cap lookup index after consuming `depth` path steps is in range and the
  comparison covers the full digest.
- The verification result is used. A path-verification helper returning `bool`
  whose value is ignored on some branch is a live class of bug — check every
  call site.
- Degenerate cases: a zero-column or empty oracle that returns success without
  hashing anything must be genuinely impossible to reach with prover-chosen
  parameters.

### Final round

- The final polynomial's coefficient count matches the claimed final degree;
  accepting more coefficients raises the degree bound.
- The final polynomial is absorbed before the final grinding and final query
  draw.
- The verifier evaluates the final polynomial itself at the final folded points
  and compares against the folded query values — for every query, not just the
  first.

## Binding the PCS to the GKR claim

The seam between the two phases is a high-yield location.

- The evaluation point passed to the PCS is the GKR folding point: same length,
  same variable order, same LSB/MSB convention as the sumcheck used.
- The batching challenge combining multiple base-layer claims is drawn after
  all of those claims are absorbed, and the same combination is applied to both
  the claims and the polynomials.
- The claimed base-layer evaluations the PCS verifies are the ones the GKR
  final check consumed — trace the actual variables, not the names.
- Every committed base polynomial is included; a column omitted from the batch
  is unconstrained.

## Parameters and the budget

Record for the budget pass: number of rounds, folding arity per round, queries
per round, grinding bits per round, initial and final domain sizes, rate/blowup,
field size. Confirm each comes from a constant or the verifier key. Then check
the composed soundness against the claimed level — see
`grinding-and-soundness-budget-expanded.md`.

A parameter schedule stored as an array indexed by round is a common shape;
check the index used at each site is the round index and not a stale or
off-by-one value, and that the array length matches the round count.
