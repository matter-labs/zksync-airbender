# Expanded Grinding and the Soundness Budget

## Why grinding exists

Every place a prover can retry until a challenge is favourable is an attack
with cost `1/ε` retries, where `ε` is the per-attempt success probability.
Proof-of-work forces each retry to cost `2^b` hash evaluations, so an argument
with `s` bits of base soundness delivers `s + b` bits against a
grinding-capable prover. This is what lets a scheme cut query counts (and proof
size) without losing security.

Grinding is therefore load-bearing, not a formality. A verifier that checks the
nonce incorrectly, or checks it against the wrong state, silently removes `b`
bits.

## What the verifier must enforce

For every PoW step:

- **The nonce is read from the proof and verified** — never assumed, never
  skipped when `pow_bits == 0` in a way that changes the transcript shape
  relative to the prover.
- **The PoW input includes the current transcript state.** Grinding on a
  seed that does not depend on the data being protected protects nothing.
- **The threshold matches the claimed bits.** `threshold = 2^32 >> b` style
  derivations: confirm the shift direction, the handling of `b = 0` and
  `b = 32`, and whether the comparison is `<` or `<=` (a `<=` gives the prover
  one extra accepting value — negligible, but note it, and note that prover
  and verifier must use the *same* comparison or completeness breaks).
- **The state update after PoW is agreed.** If verifying the PoW replaces the
  seed, every later challenge depends on the nonce, and the prover and verifier
  must both do it. If it does not update the state, the nonce is not bound and
  a later re-grind is free.
- **The consumed output words are skipped consistently.** When the PoW check
  consumes the first output word of the new state, that word is
  *low-entropy by construction* — it has `b` leading zero bits. Any challenge
  drawn from it is biased and partly prover-predictable. Confirm the draw after
  a PoW skips exactly the consumed word, on both sides.
- **The right PoW parameter is used at the right step.** Per-round schedules
  indexed by round number are easy to index with a stale variable. Check each
  call site's index and that the schedule array length matches the round count.
- **`b` is a compile-time or key-derived constant**, never read from the proof.

## The budget

Build a table. Every row is an argument with an error term; the total must
support the claimed security level.

| Argument | Error term | Value (bits) | Grinding added | Net |
|---|---|---|---|---|

Terms to include:

- **Sumcheck / zerocheck**: `(degree × variables) / |F|`, summed over layers.
- **Batching challenges**: `(number of items) / |F|` per batch, or the degree
  of the combining polynomial.
- **Permutation / memory argument**: total element count `/ |F|`. Note that
  when keys are affine in *independent* challenges (rather than powers of one
  challenge), the collision polynomial's degree is the element count itself,
  giving an exact bound — do not apply a degree correction that the
  construction does not need, and do not omit one it does.
- **LogUp / lookups**: (table size + witness size) `/ |F|` per argument.
- **PCS proximity**: per-round query soundness `(1-δ)^q`-style terms plus
  list-decoding/conjecture-dependent terms, per the scheme's own analysis.
- **PCS out-of-domain**: `degree / |F|` per OOD sample.
- **Hash**: collision resistance at the *configured* parameters. A
  reduced-round hash variant is a distinct security assumption; record it
  explicitly and check whether the repository documents an analysis for it.

Field size: use the **extension** field if challenges are drawn there, and
round *down* (a lower bound on `|F|` gives an upper bound on error — the
conservative direction). Confirm the code's constant does the same; rounding
the wrong way is a real, quiet overstatement.

## Reconcile with the code

- Find where the security level is defined and how each parameter is derived
  from it. A derivation expressed in code (`pow = max(0, target - base)`) is
  auditable; a table of magic numbers is not — for a table, re-derive the
  numbers independently and compare.
- Check that the derivation's *inputs* are correct: the assumed element count
  ceiling, the assumed field size, the assumed degree. An input that is a
  policy choice ("we assume at most `2^40` elements") must be enforced at
  runtime against the actual proof, or it is an assumption, not a bound.
- Check every security level the build supports, not just the default. Levels
  are usually feature-gated; confirm the gates are mutually exclusive and that
  the wrong combination fails to compile rather than silently selecting one.
- Check that the *deployed* configuration is the one you analyzed.

## Findings in this class

State the bits lost and how, and whether the loss is against the claimed level
or against the design's own stated margin. A grinding bug that reduces 100-bit
security to 81-bit security is a finding; a 2-bit conservative margin the
design deliberately took is not. Read the code's own comments on margins before
classifying, and if the margin's justification is absent, report it as a
specification question rather than as a soundness finding.
