# Project Profile — Airbender GKR Verifier

**Profile ID:** `airbender-gkr-verifier/v1`
**Validated against:** `zksync-airbender`, branch `mb_gkr_compiler`,
commit `e072ba30a3b738375b0cc9cc1b04767065d2a52d` (2026-08-14).
**Scope:** the GKR + WHIR verifier, unrolled/unified aggregation and recursion
statement, and the in-progress generated Solidity/Yul verifier path. Not the
prover, not the circuits.

This profile is a **search checklist and a map**, not an oracle. Every claim
below was read from the snapshot above; re-verify each against the checkout in
front of you before relying on it, and record the delta.

## Applicability check

Apply this profile only if all hold:

1. `verifier_common/` and `verifier_generator/` exist, and
   `verifier_common/src/lib.rs` exposes `verify_impl` calling `verify_gkr` then
   `verify_whir`.
2. `verifier_generator/src/gkr/` and `verifier_generator/src/whir/` exist —
   the verifier is **generated** per circuit, so the audit target is generator
   output, not hand-written verification code.
3. The transcript is Blake2s-based: `transcript/src/blake2s.rs` defines
   `TranscriptState`, `CommitBuf`, `Seed`.
4. Proof data is consumed from a `NonDeterminismSource`, not deserialized.

If 1–4 hold but details differ, treat the differences as the version delta and
re-derive them. If the checkout has quotient composition and FRI instead of
layer sumchecks and WHIR, use `stark-deep-fri.md` instead.

Apply the EVM subsection only when `verifier_evm/src/generator/`,
`verifier_evm/src/templates/`, and `verifier_evm/src/flatten.rs` exist. If the
deployed L1 verifier lives elsewhere, build a fresh deployment profile and use
`evm-l1-verifier.md`; do not project this prototype's contract split onto it.
The EVM path is a distinct Proth120/Keccak proof-system instance, not a byte-for-
byte port of the BabyBear-extension/Blake2s recursive verifier. Compare each
implementation only with its same-instance mirror/flattener and audit the
statement boundary between instances.

## Architecture in one paragraph

The verifier is a `no_std` Rust program generated per circuit family and
compiled for RISC-V, so that verification can itself be proved. It reads the
proof word-by-word from a non-determinism oracle, maintains a Blake2s
transcript, verifies a GKR layer chain down to the committed base layer, then
verifies a WHIR opening of that base layer. A separate aggregation statement
runs many such verifiers, multiplies their memory accumulators together, and
checks the global permutation identity plus the program-identity/recursion
binding.

## File map

| Concern | Path |
|---|---|
| Verifier entry, `verify_impl`, security-level PoW derivation | `verifier_common/src/lib.rs` |
| Initial transcript construction, GKR output struct, gate types | `verifier_common/src/gkr/mod.rs` |
| PoW read/verify, query-index draw, Merkle path check, leaf hashing | `verifier_common/src/whir/mod.rs` |
| Field-element read helpers, `BitSource`, fold buffers | `verifier_common/src/structs.rs` |
| Transcript primitives: seed, commit, draw, PoW | `transcript/src/blake2s.rs`, `transcript/src/pow.rs` |
| Field element canonicalization | `field/src/baby_bear/base.rs`, `non_determinism_source/src/lib.rs` |
| GKR verifier generator (layers, sumcheck, outputs) | `verifier_generator/src/gkr/mod.rs`, `.../standard_layer.rs`, `.../dim_reducing_layer.rs` |
| WHIR verifier generator (rounds, queries, final) | `verifier_generator/src/whir/rounds.rs`, `.../common.rs` |
| Generated transcript/sumcheck helpers | `verifier_generator/src/utils/transcript.rs`, `.../sumcheck.rs` |
| Aggregation / full statement, recursion chain | `full_statement_verifier/src/unrolled_proof_statement.rs`, `.../unified_circuit_statement.rs`, `.../recursion_chain.rs` |
| EVM generator, Solidity/Yul templates, and proof flattener | `verifier_evm/src/generator/`, `verifier_evm/src/templates/`, `verifier_evm/src/flatten.rs` |
| Generated EVM artifacts and two-transaction integration | `verifier_evm/generated_contracts/` |
| EVM transcript parity claim | `verifier_evm/gkr_transcript_reference.md` |
| Negative tests | `verifier/tests/corruption.rs`, `verifier/tests/malicious.rs` |
| Protocol intent | `docs/subarguments_used.md`, `docs/philosophy_and_logic.md` |

**Audit the generated code.** `verifier_generator` emits the verifier as a
token stream. Reading only the generator's control flow will miss what a
particular circuit configuration actually emits. Generate for the target
circuit (`verifier_generator/tests/generate_verifiers.rs`) and read the output,
or trace each `quote!` block to the configuration that selects it.

## Transcript mechanics — the repo-specific hazards

These are the mechanics a generic Fiat–Shamir checklist will not surface.
Verify each still holds, then use them.

### 1. `commit` is `H(seed ‖ data ‖ zero-pad)`, one call per group

`CommitBuf` lays out `[seed | data | zero-pad-to-64-byte-block]` and
`TranscriptState::commit` hashes the whole buffer, replacing the seed
(`transcript/src/blake2s.rs`). Consequences:

- **Grouping is part of the transcript.** `commit(A)` then `commit(B)` is *not*
  `commit(A ‖ B)`. Anywhere prover and verifier group differently, the
  transcripts diverge. The generator comments this explicitly at the GKR layer
  boundary (`verifier_generator/src/gkr/mod.rs`, "SINGLE transcript commit …
  two separate commits would diverge from the prover's one"). Treat every
  commit site as a grouping claim to check against the prover.
- The zero-padding extent is derived from `data_words`, so the absorbed length
  is fixed by the verifier's own constant, not by the data.

### 2. `draw_raw` does **not** advance the seed on a single-digest draw

`Blake2sTranscript::draw_randomness_using_hasher` copies the *current seed*
into the first 8 output words and only re-hashes for each additional digest.
So a draw of exactly one digest leaves the seed unchanged.

**Audit rule:** every `draw` must be separated from the previous `draw` by a
`commit` or a PoW. Two consecutive single-digest draws with nothing absorbed
between them return the **same** challenge — in source this looks like two
independent challenges. Search the generated verifier for draw–draw pairs and
check the intervening state change at each.

After any draw, the seed is bit-identical to the final digest block returned as
challenge material: for one block that is the pre-draw seed; for a multi-block
draw it is the last re-hashed block. Do not model the seed as a domain-separated
hidden state. This invariant can close false mismatch leads and can create
challenge-reuse/correlation candidates when later code assumes the seed differs
from the last emitted block.

### 3. PoW replaces the seed, and its first output word is low-entropy

`verify_pow_using_hasher` hashes `seed ‖ nonce_lo ‖ nonce_hi ‖ 0…`, asserts
`state[0] <= u32::MAX >> pow_bits`, then sets `seed = state`. Because
`read_state_for_output()[0] == state[0]`, the new seed's **word 0 has
`pow_bits` leading zero bits**.

That is why draws immediately after a PoW must skip one word —
`draw_field_els_into_after_pow` and `draw_single_field_el_after_pow`
(`verifier_generator/src/utils/transcript.rs`) draw one extra word and discard
the first. `draw_query_indices` (`verifier_common/src/whir/mod.rs`) skips the
first word for the same reason.

**Audit rule:** at every PoW site, confirm (a) the following draw uses the
`_after_pow` variant, (b) the prover skips the same word, (c) the skip is
exactly one word, and (d) any implementation in another language does the same.
A missing skip yields a challenge whose top `pow_bits` bits are known.

Note the assert uses `<=`, so the accepting set is `threshold + 1` values; both
sides must use the same comparison or completeness breaks.

### 4. Field elements are normalized at read time; the transcript absorbs the
normalized word

`read_reduced_field_el` → `NonDeterminismSource::read_field_element`. On the
host path this is `from_raw_repr_with_reduction` (two conditional subtractions,
sufficient for any `u32` against this modulus). On RISC-V, `CSRBasedSource`
reads via `csrrw` + the `MOP_ADD_MOD` machine op and then
`from_reduced_raw_repr`, i.e. the reduction is performed by the machine
operation rather than in Rust. Absorbed data is `…as_u32_raw_repr()` of the
already-normalized element.

This subsection is specific to the BabyBear `u32` path. Establish the concrete
field and serialization API before applying it. `Proth120` uses 128-bit
serialization; its `as_u32_raw_repr()` and
`from_raw_repr_with_reduction()` trait methods are unreachable and cannot be
audited with the same raw-word model.

**Audit rules:** (a) confirm the guest path's reduction really is performed by
the machine op — if it is not, the guest accepts unreduced values that the host
rejects, and the two verifiers accept different proof sets; (b) confirm every
same-instance BabyBear implementation normalizes at the same point, or its transcript
diverges for non-canonical inputs; (c) confirm the same helper is used at every
absorb site — a raw `read_word` feeding an absorb that elsewhere uses
`read_reduced_field_el` is a divergence.

### 5. The initial transcript excludes its own padding

`make_initial_transcript` (`verifier_common/src/gkr/mod.rs`) builds a
`#[repr(C, align(64))]` struct
`inits_and_teardowns_top_bits ‖ external_challenges_flattened ‖ setup_caps ‖
memory_caps ‖ witness_caps ‖ padding` and hashes only up to `offset_of!(…,
padding)`. The struct-layout asserts around it are load-bearing: if a field is
added or reordered, the hashed prefix changes.

Note what is bound here: the **external challenges are inside the initial
transcript**, so per-chunk challenges are bound to them; the aggregation layer
separately re-derives those challenges (see §Aggregation).

### 6. `debug_assert!` appears in verification paths

Several layout, size, and bound assertions are `debug_assert!` — including the
cap-length bound in `verify_merkle_path` before `get_unchecked` reads, and
`debug_assert_eq!(proof_output.setup_caps.len(), 0)` in the aggregation. These
are absent in release. Classify each as: layout invariant (fine), or soundness
check (finding). Do not assume; check what the value can be.

### 7. Initialized length and storage capacity travel separately

The generated GKR initialization pushes only `evaluation_point_len` elements
into a `LazyVec`, then uses unsafe `set_len(GKR_ROUNDS)` while storing the true
logical length in `prev_point_len`. The tail is capacity, not meaningful point
data. Similar patterns occur in generated transcript, sumcheck, and WHIR
buffers.

Audit every consumer for slicing by the logical length before reads, hashing,
copying, equality, or arithmetic. A later refactor that iterates the physical
length can absorb or compute over uninitialized/stale tail elements even though
the allocation itself is large enough.

### 8. Optimizer barriers may preserve real checks

`verifier_common/src/lib.rs` masks timestamp limbs against
`core::hint::black_box(0xffff0000)` inside unconditional assertions. The barrier
is intended to prevent the compiler from proving the range check redundant and
deleting it in the guest binary. Optimization hints are not enforcement, but
the converse matters: inspect the optimized/deployed artifact and prove required
assertions survive. Removing a barrier or changing value provenance can silently
change generated verifier semantics.

## Known closures to revalidate

Keep these in the candidate-disposition ledger so later reviews do not repeatedly
file them as fresh leads. They remain closures only while the cited mechanism and
fixed schedule apply:

- **No length-prefix ambiguity inside one Blake2s commit.** `CommitBuf::commit`
  passes `seed_words + data_words` as the meaningful length, and the final Blake2s
  compression call receives the exact active-word count. Zero padding fills the
  block but is excluded from that count. Different meaningful lengths are not
  identified merely because their padded buffers match.
- **Single-digest draw state.** The seed/output identity in §2 is the implemented
  state machine, not automatically a missing state update. The candidate closes
  only when no security argument requires a fresh state or distinct draw before
  an intervening commit/PoW.

Re-derive rather than blindly trust every closure. Record source, features/target,
closing invariant, and the change that would reopen it.

## Round schedule (GKR phase)

Reconstructed from `verifier_generator/src/gkr/mod.rs`. Verify against the
generated output for your target circuit.

```text
init    seed ← H(it_top_bits ‖ external_challenges ‖ setup_caps ‖ memory_caps ‖ witness_caps)
grind   read nonce, verify PoW(LOOKUP_CHALLENGES_POW_BITS)          [advances seed]
draw    lookup_alpha, lookup_additive_challenge                     [_after_pow: skips word 0]
read    output-layer evaluations (total_output_polys × 2^out_log2)
absorb  ── one commit of all of them ──
draw    out_log2 folding challenges + 1 batching challenge          [one draw of N elements]
        claim₀ per output poly = dot_eq(evals, eq(challenges))
for each layer (outputs → base):
  for each sumcheck round:
    read    4 cubic coefficients                                    [SUMCHECK_POLY_COEFFS]
    check   (p(0) + p(1)) · eq_prefactor == claim                   [before absorb]
    absorb  the 4 coefficients
    draw    r_k                                                     [single digest]
    update  claim ← p(r_k); eq_prefactor ← (1-r)(1-p) + r·p
  read    one at-point evaluation per output poly
  check   final-step accumulator == final_claim · eq_prefactor
  read    extra cached-relation evaluations (if any)
  absorb  ── SINGLE commit of at-point evals ‖ extra evals ──
  draw    next batching challenge
  check   cache relations; virtual setup evaluations
check   LogUp identity per lookup type: acc_num == 0 && acc_den != 0
check   permutation / inits-and-teardowns products extracted from output evals
grind   verify PoW(BATCHED_PROXIMITY_POW_BITS)
draw    whir_batching_challenge                                     [_after_pow]
→ WHIR
```

Audit hot spots in this schedule:

- the split of each layer into pre-draw (read + commit extras) and post-draw
  (fold claims) — the extras must be inside the same commit as the at-point
  evals and before the batching draw;
- the final-step check consuming `state.batching_challenge` from the
  *previous* layer while the draw sets the *next* one;
- claim extraction offsets in `#output_checks` matching the prover's output
  group layout, per circuit configuration;
- `if num_x > 0` conditionals around output groups and extras — each is a
  transcript-shape branch.

## Round schedule (WHIR phase)

From `verifier_generator/src/whir/rounds.rs` and `common.rs`:

```text
per round:
  draw    ood_point                                    [single field element]
  read    ood evaluation(s)
  absorb  ood evaluations
  grind   PoW(INITIAL_POW_BITS | WHIR_POW_BITS[round])
  draw    delinearization_challenge
  sumcheck steps (verify_whir_sumcheck_step):
    read    3 quadratic coefficients
    check   p(0) + p(1) == claim                       [before absorb]
    absorb  coefficients
    draw    alpha
final:
  read    final monomials
  absorb  monomials
  grind   PoW(FINAL_POW_BITS)
  draw    query indices                                [skips word 0; BitSource, LE]
  verify  Merkle paths against caps; fold cosets
```

Parameters live in generated constants: `WHIR_FOLD_STEPS`, `WHIR_QUERIES`,
`WHIR_POW_BITS`, `FINAL_MONOMIALS_LEN`, `NUM_ORACLES`, `CAP_SIZE`. Confirm each
is derived from the security level and circuit, never from the proof, and that
per-round arrays are indexed by the round variable at every site.

Query-index mechanics: `draw_query_indices` draws `draw_words`, skips word 0,
then `BitSource::take_bits` consumes an LE bitstream. `compute_tree_index`
maps a query index to a tree position via coset masking plus a bit-reversal of
the coset part. Bit-order conventions here must match the prover and the fold
order; this is the classic silent-divergence site.

## Aggregation and the deferred challenge binding

`full_statement_verifier/src/unrolled_proof_statement.rs` implements the
pre-commitment pattern described in `docs/subarguments_used.md`:

1. Read final register values and timestamps (32 × value/ts_lo/ts_hi), assert
   `x0 == 0`, absorb them into a **separate buffering transcript**.
2. Read and absorb final pc / final timestamp.
3. Read the external challenges from the oracle — **used before being
   derived**.
4. For each circuit family: read a circuit count, absorb a family separator
   (only when count > 0), then per circuit run the generated verifier, absorb
   its memory caps, compare its setup cap against the expected one, and
   multiply its read/write accumulators into the globals.
5. Same for the inits-and-teardowns circuit, plus the check that the
   `inits_and_teardowns_top_bits` form the exact sequence `0,1,2,…`.
6. Assert the buffering transcript sits on a block boundary.
7. Same for delegation circuits, accumulating
   `num_permutation_terms_per_circuit`.
8. Assert `total_permutation_elements < 1 << MAX_PERMUTATION_ELEMENTS_LOG2`.
9. Finalize the buffering transcript, read the PoW nonce, **re-derive the
   external challenges, and assert equality with the ones used in step 3**.
10. Inject the machine-state read/write contributions and assert
    `read_accumulator == write_accumulator`.
11. Build the public output: registers 10–17, plus the end-parameters hash
    (final pc with timestamps zeroed, and every family's setup cap) and the
    recursion-chain value.

Audit this list item by item. The soundness of steps 3–9 rests entirely on the
completeness of what is absorbed in 1–7 and on step 9 dominating every return
path. Specific things to verify in the checkout:

- every family that contributes accumulators also absorbs its caps and its
  separator, including the zero-count case;
- the setup-cap comparison runs for every family, and the expected caps come
  from the verifier key rather than the proof;
- the cycle accounting: establish what pins each chunk's trace length, trace the
  chain from setup cap → circuit size → counted cycles, and write it down rather
  than assuming a source constant matches the accepted circuit;
- `MAX_CYCLES` versus the timestamp range the memory argument needs;
- the recursion-chain branch where the chain is *not* extended (preimage's
  second half equals the current end parameters) — check a prover cannot steer
  into it to drop a link;
- `BASE_LAYER` versus recursion-layer separation.

## Security levels and PoW derivation

`verifier_common/src/lib.rs` derives `MEMORY_DELEGATION_POW_BITS` from the
security level:
`base = field_size_log2 - max_elements_log2 - 2`, then
`pow = max(0, security_bits - base)`, with `BABYBEAR_EXT4_SIZE_LOG2 = 123`
(floored, the conservative direction) and `MAX_PERMUTATION_ELEMENTS_LOG2 = 40`
(a policy ceiling, enforced at runtime by the assert in step 8 above). The
`- 2` is documented as a deliberate margin rather than a degree correction.
`security_80` and `security_100` are mutually exclusive features.

When auditing the budget: re-derive these numbers independently, check the
runtime assert really enforces the policy ceiling on the actual proof, and
check both security levels.

## Cross-implementation relationship

There are two concrete proof-system instances, not three interchangeable ports:

- the generated recursive/native verifier and host prover use the profiled
  BabyBear-extension/Blake2s instance and must match each other exactly;
- `verifier_evm/` verifies a Proth120/Keccak packed-calldata outer proof. Its
  Solidity/Yul must match its Proth120 Rust mirror, flattener, generator, and
  deployed bytecode—not the BabyBear proof byte stream.

First determine which instance is deployed for each layer and what statement
crosses the boundary. Proof portability across the instances is neither expected
nor a parity requirement. The outer instance must authenticate the recursive
verifier program/setup and public outputs attesting to the inner whole-program
statement.

`verifier_evm/gkr_transcript_reference.md` is a parity claim and can drift.
Compare the production Rust paths in `src/seed.rs` and `src/flatten.rs` with the
generated Solidity byte-for-byte and challenge-for-challenge. A Rust test that
validates a Rust mirror does not establish equality with deployed Yul.

## EVM/L1 snapshot and incompleteness gates

At this snapshot, `verifier_evm::generate_verifiers` produces a Proth120/Keccak
GKR verifier, a WHIR verifier, and a registry. GKR and WHIR run in separate
transactions and independently commit to a handoff preimage containing the
post-GKR seed, batching challenge, opening, evaluation point, and both base
caps. The registry is intended to record when both halves marked the same
commitment.

The generated GKR path verifies one selected circuit artifact. Its local
permutation equality is a whole-statement memory check only if this proof is
indeed the single outer unified chunk and already contains all initial/final
machine-state contributions. Do not infer this from the contract name or the
fact that the original base execution was recursively aggregated.

Important current-profile revalidation gates:

- locate the code that authenticates the outer recursive verifier program/setup,
  successful final PC, base program output, and expected chain digest before a
  state transition;
- derive the authorized caller set for every registry mutation and the exact
  condition the settlement caller treats as completed verification;
- trace every low-level registry call's success and returndata into rejection or
  prove that the notification is non-authoritative;
- audit idempotence, overwrite, replay, cross-version, and cross-deployment
  behavior at the real settlement caller;
- state exactly what honest integration tests establish, then separately test
  authorization, recursive-chain closure, adversarial calldata rejection, and
  final L1 settlement semantics.
- current Rust calldata construction obtains several WHIR handoff fields from
  prover-recorded proof fields rather than replaying GKR. The split remains
  sound only because the GKR half independently derives and commits the exact
  same complete state and authenticated linkage requires equality.
- GKR initial transcript encoding mixes LE `u32` words with later BE field
  elements/nonces and raw digests. Treat the flattener/template inverse as a
  byte-level obligation.
- the GKR template uses `assembly ("memory-safe")` with a manually documented
  spill region under `viaIR`; prove the annotation and every generated memory
  bound for the exact compiler/settings/runtime bytecode.
- trusted setup inputs are an artifact supply-chain boundary. Trace
  `DELEGATION_CIRCUITS_SETUP_PARAMS`, every
  `full_statement_verifier/src/imports/*` generated module, circuit-family setup
  caps, unified setup, final-PC constants, and security parameters back to the
  intended program/circuit artifacts. Regenerate and compare when supported;
  equality against a stale or wrong compiled constant verifies the wrong program
  consistently.

Use `evm-l1-verifier.md` for the complete on-chain review method and deployment
trust map.

## Existing negative tests

`verifier/tests/corruption.rs` already covers: garbage proof, corruption at
fractions, corrupted GKR region, corrupted WHIR region, zeroed regions, shifted
non-determinism stream, corrupted oracle caps, truncated stream, corrupted
final monomials, cross-circuit stream substitution, corrupted
init/teardown bits, non-canonical field element, corrupted OOD sample,
corrupted PoW nonce (general, lookup, batched-proximity), corrupted cache
relations, and corrupted init/teardown evaluations.

Use this as the baseline coverage map. For every row of your prover-freedom
ledger, name the test that covers it; rows with no test are where regressions
will land, and that gap is itself reportable.

## Maintenance

Update this profile when the transcript primitives, the generated round
schedule, the aggregation statement, recursion-chain ABI, EVM contract split,
registry/settlement boundary, compiler configuration, or security-level
derivation change.
Record the new commit, re-run the applicability check, and re-verify each
numbered hazard in §Transcript mechanics — those are the claims most likely to
silently rot.
