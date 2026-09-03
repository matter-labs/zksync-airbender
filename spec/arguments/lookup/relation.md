# Lookup relation

## Inputs

- **`IN-LOOKUP-001` — Generic table.** Fixed semantic-table rows followed by the
  program decoder rows, zero-padded to the circuit trace length.
- **`IN-LOOKUP-002` — Virtual tables.** `T16 = {0,...,2^16-1}` and
  `T19 = {0,...,2^19-1}`, each padded to the trace length.
- **`IN-LOOKUP-003` — Queries.** Generic, 16-bit, and timestamp queries emitted by
  the compiled circuit. The decoder query is weighted by `execute`.

## Relation requirements

- **`REQ-LOOKUP-REL-001` — Row encoding.** A generic row is the lookup values,
  zero-padding, and a table ID when the setup contains more than one table class.
- **`REQ-LOOKUP-REL-002` — Multiplicity.** For each channel and setup row `t`, the
  witness multiplicity equals the number of active queries equal to `t`.
- **`REQ-LOOKUP-REL-003` — Rational identity.** With transcript challenges
  `(alpha, beta)`, a channel represents
  `sum_q a_q/(beta + enc_alpha(q)) - sum_t m_t/(beta + enc_alpha(t))`.
- **`REQ-LOOKUP-REL-004` — Local output.** Each present channel exports a
  numerator/denominator pair. The three output classes are the 16-bit range,
  timestamp range, and generic lookup channels.

## Acceptance requirements

- **`REQ-LOOKUP-VER-001` — Challenge order.** Check lookup grinding before sampling
  `(alpha,beta)`, and sample them only after the commitments they bind.
- **`REQ-LOOKUP-VER-002` — Term pairs.** Represent each query term by
  `(a_q,beta+enc_alpha(q))` and each table term by
  `(-m_t,beta+enc_alpha(t))`.
- **`REQ-LOOKUP-VER-003` — Pair accumulation.** A pair `(n,d)` represents `n/d`.
  Starting from `(N,D)=(0,1)`, combine every pair by
  `N <- N*d+n*D` and `D <- D*d`.
- **`REQ-LOOKUP-VER-004` — Terminal identity.** Accept a channel only if `N=0` and
  `D!=0`. Checking only the numerator is insufficient.
- **`REQ-LOOKUP-VER-005` — All channels.** Apply the terminal check independently
  to the 16-bit, timestamp, and generic lookup outputs.

## Reduction assumptions

- **`REQ-LOOKUP-INT-001` — Output map.** Every present lookup class maps to exactly
  one terminal pair and one relation.
- **`REQ-LOOKUP-INT-002` — Setup binding.** Generic setup columns are committed;
  range and timestamp setup polynomials are reconstructed by the verifier.
- **`REQ-LOOKUP-INT-003` — GKR preservation.** Every pair-combination and
  dimension-reduction layer preserves the represented rational value. The terminal
  reduction yields exactly 16 pairs per present channel.
