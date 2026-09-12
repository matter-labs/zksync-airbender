# Proof-Input Validation

The pass that enumerates prover freedoms rather than verifier checks.

## The ledger

Walk the proof stream in read order. One row per value the prover supplies —
not per check the verifier performs.

| Value | Where read | Domain the code accepts | Domain the protocol requires | What pins it | Status |
|---|---|---|---|---|---|

`What pins it` must be one of:

- **transcript binding** — absorbed before every challenge that must detect a
  wrong value, and some later check is probabilistically sound given that;
- **algebraic check** — an equation the verifier evaluates and compares;
- **commitment opening** — a Merkle path (or equivalent) verified against a
  root/cap that is itself bound;
- **recomputation and comparison** — the verifier derives the value
  independently and compares, with the comparison result actually used;
- **structural impossibility** — the value cannot vary (compile-time constant,
  fixed-size array with no length field).

Anything else — "the honest prover sends the right value", "it would fail
later", "the type is `u32`" — is not a pin. Type is not a pin: a `u32` field
element still has non-canonical representatives, and a `usize` index still
exceeds an array.

Status: `pinned`, `unpinned`, or `partially pinned` (with the residual freedom
named).

## How the proof arrives

Establish the transport before auditing values, because it determines which
attacks are structurally possible.

- **Deserialized struct.** Lengths, counts, and tags are in the data. Audit
  length fields, count fields, enum tags, and the deserializer's own error
  paths. A count read from the proof is a transcript-shape parameter (see
  `fiat-shamir.md`).
- **Streamed oracle / non-determinism source.** The verifier pulls a fixed
  number of words in a fixed order determined by its own code. There are no
  length fields to attack — but the compensating risks are:
  - **stream re-alignment**: shifting the stream by one word makes every later
    value a different prover-chosen value. Only the checks reject it, so
    confirm the checks are dense enough that no shifted stream can pass.
  - **cross-context substitution**: feeding one chunk's or circuit's proof
    stream to another verifier. Only transcript/domain separation and
    setup-identity checks reject it.
  - **truncation**: what happens when the stream runs out mid-verification —
    abort, or a default value?
- **Calldata / external buffer.** Add byte offsets, widths, endian/lane
  extraction, bounds, pointer arithmetic, final-cursor exhaustion, and
  trailing-data rules to the ledger. On EVM/Yul, out-of-range calldata access
  can supply zero-padded data instead of a Rust-style EOF error, so prove that
  every truncated prefix rejects. Record every external call/registry write
  that carries a parsed value onward, including target authentication, checked
  success/returndata, overwrite/replay behavior, and final settlement use. Use
  `evm-l1-verifier.md` for the complete on-chain pass.

## Canonicity and encoding

The most common unpinned-value family.

Establish the concrete field and serialization API before applying a
canonicity checklist. A `u32` raw-representation analysis for BabyBear does not
transfer to a 128-bit Proth field, a limb-encoded large field, or an extension
whose coefficients use a different parser. Record the accepted byte/word type,
modulus, canonical constructor, reduction helper, and transcript encoding for
each concrete verifier instance first.

For each field element the prover supplies:

- Is the raw word reduced into the field, or trusted as already canonical?
- Does that answer differ by target architecture, feature, or code path? A
  host path that reduces and a guest path that does not is a real, exploitable
  asymmetry — the deployed path is the one that matters, and the tested path is
  usually the other one.
- Is the value **absorbed** as the raw word or as the canonical word? If raw,
  two representations of the same element give different transcripts (prover
  gets a free challenge-perturbation oracle). If canonical while the algebraic
  use is raw, the transcript does not bind what is used.
- Extension-field elements: is each coefficient handled the same way, and is
  the coefficient order the same on absorb and on reconstruct?

For each integer the prover supplies (indices, counts, nonces, bit fields,
addresses, timestamps):

- What is the accepted range, and what is the required range?
- Is a bit-width limit enforced by a check, or only by how the value is used?
- Are high bits masked (silently accepting garbage) or checked (rejecting it)?
  Masking is fine only when the masked-away bits genuinely cannot matter —
  prove that, do not assume it.

## Values that are both sent and derivable

A recurring bug shape: the verifier can compute a value but also reads it, for
efficiency or for structural convenience.

For each such value confirm the verifier **compares** the two, that the
comparison covers every component (not just the first limb or the first word),
and that the comparison result reaches the reject path. A recomputation whose
result is dropped is worse than no recomputation — it reads like a check.

Instances to look for:

- cached or memoized relation evaluations the prover supplies to save verifier
  work, which must be re-derived and compared;
- claimed outputs that also appear as inputs to a later round;
- duplicated commitments/caps that must equal a setup or a previous chunk's;
- values echoed between phases (a claim carried from the sumcheck into the
  PCS opening).

## Indices and bounds

Every prover-influenced index that reaches an array access:

- Where does it come from — drawn from the transcript (bounded by the draw
  width), read from the proof (unbounded), or derived (bounded by its inputs)?
- Is the bound enforced by `assert!`, by `debug_assert!` (compiled out), or by
  nothing before an unchecked access?
- For query indices: is the number of bits drawn exactly the index bit-width,
  and is the mapping from bits to positions injective and full-range?
- For tree/leaf indices: does the index range match the tree depth and cap
  size, and is the cap lookup in range?

Unsafe indexing on a prover-derived index is simultaneously a memory-safety
bug and, if it can be steered to read a value that makes a check pass, a
soundness bug. Trace what the out-of-bounds read would return before
classifying it.

## Shape parameters

Values that determine how much data is read or how many rounds run:

- round counts, layer counts, query counts, folding factors, degree bounds,
  cap size, trace length / number of variables, chunk counts, delegation
  counts.

For each: is it a compile-time constant, part of the verifier key/setup, or
read from the proof? Only the first two are safe by default. Anything read
from the proof must be bound into the transcript *and* checked against the
protocol's requirement, and lowering it must not lower security (a prover who
picks fewer queries or fewer grinding bits picks its own security level).

## Optional and conditional data

Every `if` that guards a read:

- What determines the condition — a constant, the verifier key, or the proof?
- Does the prover-visible behaviour differ between the branches in a way the
  transcript does not record?
- Is the "absent" case distinguishable from the "present but empty" case?

## Zero, one, and degenerate values

Try the degenerate assignment for every prover-supplied value and ask whether
any check becomes vacuous:

- zero challenges or zero claimed values that make a product or a difference
  trivially zero;
- an all-zero proof region (does every check still bite?);
- a claimed inverse of zero;
- empty structures: zero queries, zero layers, zero columns, an empty cap —
  does the corresponding verification loop then verify nothing and return
  success?
- repeated values where distinctness is assumed (two identical query indices
  halve the query count; identical challenges collapse a batch).

An empty-container early return that yields `true` is the single most common
vacuous-success shape. Search for it directly.

## Regression properties

For every unpinned value found, state the negative test that would have caught
it: corrupt exactly that value in a valid proof and assert rejection. A mature
verifier will already have a corruption-test harness organized by region
(garbage, zeroed regions, shifted stream, truncated stream, corrupted caps,
corrupted nonces, non-canonical elements, cross-context substitution). Map your
ledger onto that harness and report which ledger rows have no corresponding
test — an unpinned value with no negative test is the one that will regress.
