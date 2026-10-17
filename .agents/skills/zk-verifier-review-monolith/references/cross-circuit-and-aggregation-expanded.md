# Expanded Cross-Circuit and Cross-Chunk Composition

Individually valid proofs do not compose into a valid statement for free. This
pass audits the layer that combines them — historically the richest source of
soundness bugs in chunked machine architectures, because no single circuit
review and no single verifier phase covers it.

## The composition question

Write the aggregate statement in one sentence, then ask what would have to be
true for it to follow from the per-chunk statements. Typically:

> Program `P` (identified by its setup/preprocessing commitment), started in
> state `S₀`, executed for `N` cycles and ended in state `S₁`, with a globally
> consistent memory.

Each chunk proves only: "some `2^k` consecutive cycles executed correctly,
contributing these accumulator values". Everything connecting the chunks —
identity, ordering, coverage, memory closure — is the aggregation layer's job.

## Global memory / permutation argument

The standard construction: every memory access contributes to a read set and a
write set; `init + write set` must be a permutation of `teardown + read set`;
the equality is checked as a product of linearized keys under shared random
challenges.

Verifier-side obligations:

- **Every chunk's contribution is accumulated.** Walk each circuit family,
  including delegation circuits and the init/teardown circuit, and confirm each
  proof's read/write accumulators multiply into the global accumulators. A
  family whose accumulator is computed but not multiplied in is a silent hole.
- **The final equality is checked** — read accumulator == write accumulator —
  unconditionally, after all contributions including any verifier-injected
  ones.
- **Verifier-injected contributions are correct.** The aggregation layer often
  injects the machine-state (pc/timestamp) contribution and the
  register-teardown contribution itself, from values it treats as public. Those
  injected terms must be built from values the verifier has bound (absorbed
  registers, final pc/ts), with the same linearization challenges and the same
  key encoding the circuits used. An encoding mismatch here is undetectable by
  any circuit review.
- **The shared challenges are the same for every chunk.** Each per-chunk
  verifier must be invoked with the identical challenge tuple, and every field
  of the tuple must be compared — not just the first element.
- **Element-count bound.** The permutation argument's Schwartz–Zippel error is
  (total elements)/|F|. The verifier must bound the total element count against
  the value the security analysis assumed, counting main-circuit and
  delegation contributions separately if they scale differently. Check that the
  count actually accumulated matches what the code checks.

## Deferred challenge binding (pre-commitment)

A common optimization: the memory-related trace columns are committed *first*,
challenges are derived from those commitments, and the chunk proofs are then
produced in parallel using those "external" challenges. The recursive verifier
therefore receives the challenges out-of-band, uses them throughout, and only
at the **end** rebuilds the transcript from the accumulated commitments and
asserts the challenges match.

This is sound only under all of:

1. **Every commitment that fed the original derivation is re-absorbed**, in the
   same order, with the same grouping and encoding — including the per-family
   separator values, the delegation-type tags, and any counts.
2. **The re-derivation reproduces the full derivation**, including any grinding
   nonce, and the nonce is read from the proof and verified, not assumed.
3. **The equality check covers every challenge component** and is
   unconditional.
4. **No accepted output escapes before the check.** If the function returns a
   public output, the check must dominate every return path.
5. **The buffered transcript's state is unambiguous at the check point** —
   e.g. an assert that the absorb buffer sits exactly on a block boundary, so
   that different absorb sequences cannot produce the same finalization.

Audit each numbered item separately. Item 1 is where bugs live: a family with
zero circuits that skips its separator absorb, or a cap absorbed in a different
grouping than the pre-commit phase used.

## Chunk coverage, ordering, and identity

- **Setup identity.** Each chunk's setup/preprocessing commitment must be
  compared against the expected value for its family. Since the setup encodes
  the program, this is what binds the proof to "which program". Confirm the
  comparison is done for every family including delegation circuits, and that
  the expected values come from the verifier key, not the proof.
- **Family/type tags** are absorbed so a proof of family A cannot be presented
  as family B.
- **Cycle accounting.** How does the verifier know how many cycles were proved?
  If the per-chunk cycle count is a hardcoded constant rather than bound to the
  proof, then a chunk proving fewer cycles than assumed inflates the counted
  total. Establish whether the trace length is pinned by the setup commitment
  (usually yes, since the setup is size-specific) and record the chain
  explicitly — this is a frequently assumed, rarely written-down link, and a
  `TODO` near the accounting is a strong signal to check it.
- **Total-cycle bound** against the timestamp range: the timestamp encoding
  supports a fixed number of cycles before wrapping, and wrapping breaks the
  `read_ts < write_ts` ordering that makes the memory argument sound. The
  verifier must enforce the bound it assumed.
- **Ordering.** Does the argument require chunks in execution order, or is any
  order acceptable given the pc/timestamp continuity is carried through the
  memory argument? Establish which, then check the code enforces what is
  required. Most designs make order irrelevant *because* continuity rides on
  the global argument — confirm that claim rather than assuming it.

## PC and timestamp continuity

The claim "each cycle reads its own pc at its own timestamp" is usually not a
single constraint but an emergent property of: monotone timestamp increment per
cycle, pc update per the ISA, the machine-state tuple riding the global memory
argument, and correct init/teardown. Audit it as a chain:

- the initial state is bound (public input, or injected by the verifier);
- the final state is bound and exported;
- the per-chunk boundary states are connected only through the global argument
  — so any circuit that can emit a machine-state tuple with a free pc or
  timestamp breaks continuity globally, not locally;
- init/teardown circuits enforce the address-uniqueness/ordering discipline the
  argument requires, and the verifier checks the parts of that discipline it
  owns (for example that the set of address-range top bits forms the expected
  complete, non-repeating sequence).

## Delegation / precompiles

Delegation lets a main circuit request work from a specialized circuit through
a one-sided contribution to a shared argument, fulfilled by the other side in a
different chunk.

- **Both sides use the same challenges and the same tuple encoding.**
- **The delegation type is a constant per circuit** on the fulfilling side and
  is absorbed on the aggregation side.
- **Unprocessed requests cancel.** When the "should process" flag is false, all
  contributed fields must be forced to values that cancel in the sets. This is
  a circuit obligation, but the verifier owns the *count* bound that makes the
  argument sound.
- **Row-count bound.** Set-equality via a log-derivative-style argument with
  boolean multiplicities is only sound if the number of contributing rows is
  below the field characteristic; otherwise a prover can wrap multiplicities.
  The verifier must check the total. Find that check.
- **Address-space separation.** Delegation ABIs place parameters at derived
  addresses; the verifier's role is to confirm the address-space partitioning
  parameters it supplies are the ones the circuits assumed.

## Padding and inactive rows

Chunks are power-of-two sized, so real work is padded. Padding must be
argument-neutral.

- Padding rows must contribute identity elements to every global accumulator,
  or contribute matched read/write pairs that cancel.
- The verifier owns any parameter that determines where padding starts. If that
  boundary is prover-chosen and unbound, a prover can relabel real rows as
  padding.
- Check the degenerate case: a chunk that is entirely padding must contribute
  identity, and must not be able to absorb a separator that shifts the
  aggregation transcript.

## Public output and recursion binding

The aggregation layer emits a public output that a subsequent layer or an
on-chain verifier consumes.

- **The output is a function of bound values only.** Trace each output word to
  an absorbed or verifier-derived source.
- **The ending state is pinned.** Ending pc must be checked against the
  expected termination convention, so that "the program finished" is part of
  the statement rather than "the program stopped somewhere".
- **The program identity is in the output.** The setup commitments must be
  hashed into the output (or otherwise bound), or a proof of program A is
  accepted as a proof of program B.
- **Recursion chain.** When a layer continues a chain, the previous chain value
  must be bound into the new one such that the chain cannot be forked,
  truncated, or reordered. Audit the chain hash's preimage structure: is the
  preimage supplied by the prover and checked against a bound digest, and does
  the check cover every word? Is there a branch where the chain is *not*
  extended, and can a prover force it?
- **Layer separation.** Base-layer and recursion-layer statements must not be
  interchangeable; find the value that distinguishes them.

## Cross-implementation and cross-version composition

- A proof produced for one security level must not verify under another if the
  parameters differ; find what separates them.
- If several verifier implementations mirror the same proof instance, their
  accepted sets must match; independent proof instances instead require an
  authenticated statement handoff (see `fiat-shamir.md` §8).
