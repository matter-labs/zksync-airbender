# L1 wrap transcript and calldata recipe

The registered bundle combines the 2^21 Proth120 circuit, the committed wrap proof
and its `OperationMode::SingleChunk` boundary state. The complete `ProverConfig`
selects packing, commitment mode and WHIR geometry; the auxiliary data carries
external-challenge PoW and the boundary state, with no packing field. The bundle
paths and resolved configuration live in [the version descriptor](tests/common/mod.rs).

## Transcript initialization

[seed.rs](src/seed.rs) reconstructs the initial preimage in this order:

1. For each of the 32 final registers, its value and split timestamp
   `(value, timestamp_low, timestamp_high)`.
2. The final PC and split final timestamp.
3. `proof.inits_and_teardowns_top_bits`.
4. The setup cap's digest words.
5. The merged memory-and-witness cap's digest words.

Each word is serialized as a little-endian u32. Keccak256 of the concatenation is
`commit_initial_u32`'s seed. This encoding differs from digest words on the WHIR
wire, which are big-endian u32s. Proth120 has modulus `7 * 2^120 + 1`; field
absorptions use 16-byte big-endian values, and PoW nonces use eight big-endian bytes.
A PoW step absorbs its nonce even when the configured difficulty is zero.

## GKR transcript order

[replay_gkr_points](src/encoding/replay.rs) follows the prover's absorptions and
draws to the WHIR handoff:

1. Absorb the external-challenge PoW nonce, then draw the external and lookup
   challenges.
2. Absorb explicit output evaluations in `OutputType` map order, each read or
   numerator vector followed by its write or denominator vector. Draw the output
   evaluation point, then its batching challenge.
3. Process dimension-reducing layers in descending index order. For each round,
   absorb its multilinear coefficients and draw the round challenge. Absorb the
   layer's final LSB-line pairs in map order, then draw the last-coordinate and
   next-batching challenges. The next point starts with that last coordinate,
   followed by the round challenges.
4. Process circuit layers from the highest layer to zero. Absorb each round's
   multilinear coefficients before drawing its challenge. At the layer boundary,
   absorb the at-point evaluations followed by cached-relation evaluations, both
   in map order, then draw the next batching challenge.
5. Draw `config.pack_log2` extra coordinates, absorb the batching PoW nonce and
   draw the WHIR batching challenge. The resulting seed must equal the proof's
   `intermediate_transcript_seed`.

This replay checks transcript order, shape and the recorded handoff seed. It does
not verify claims or PoW difficulty. `gkr_whir_handoff_seed` itself only reads the
recorded seed. The generated Solidity verifier checks the GKR relations and WHIR
openings; the Rust replay is an encoding oracle.

## Packing and the WHIR boundary

The [CPU prover](../prover/src/gkr/prover/mod.rs) concatenates memory claims then
witness claims for the merged oracle; setup claims remain separate. Packing
appends the extra coordinates to the base-layer point. Within each packed group,
claims are folded as adjacent pairs in coordinate order, using
`a + (b - a) * r`; a short final group is zero-padded.

Batching PoW uses the configuration's WHIR message size and base LDE together with
`committed_base_oracle_columns(circuit, config.pack_log2,
config.merged_memory_and_witness())`. The raw column census is not the packed
oracle count. Circuit ranges, the proof and the resolved configuration determine
the layer counts and dimensions; this recipe does not pin a retired shape.

## Wire encoding and the verified statement

[F1](src/encoding/mod.rs) encodes timestamp runs, field-element runs and 25-byte
digests. The decoder reconstructs the transcript memory image; deployment data
supplies the setup cap, term table and final PC.
The deployed F1 decoder reconstructs transcript values and rejects unconsumed input. The [WHIR template](src/templates/whir.sol) verifies openings after the
GKR-to-WHIR handoff.

The statement reported to `IVerificationRegistry.markVerified` is the 96-byte tuple
`publicInput || auxInput || setupCommitment`. The first two words concatenate final
register values x10..x17 and x18..x25 respectively as little-endian u32s. The last
word is Keccak256 of the setup cap serialized as big-endian u32 digest words;
[verified_mark](src/seed.rs) computes the same tuple.

## Committed checks and regeneration

- [replay_reaches_the_recorded_handoff_seed](tests/encoding_roundtrip.rs) checks
  the replay against the proof's recorded seed.
- [e1_factorization_including_degenerate_points](tests/encoding_roundtrip.rs)
  checks round factorization at the exceptional challenges as well as ordinary points.
- [run_merged.sh](generated_contracts/run_merged.sh) checks actual proof acceptance,
  rejection controls and deployed-code sizes on the EVM.

Run the Rust checks with `cargo test -p verifier_evm --tests`. Run the
cryptographic verifier with
`cd verifier_evm/generated_contracts && ./run_merged.sh --no-gas`.
The Rust transcript checks do not replace this Foundry gate.

For proof regeneration, use `REGENERATE` in
[prover_pipeline/src/l1_reference.rs](../prover_pipeline/src/l1_reference.rs),
then its setup-frontier export. The EVM producers read the canonical bundle directly.
The [contract harness README](generated_contracts/l1_wrap_2p21/README.md) gives the
contract and calldata producer commands. `checked_in_contracts_are_current` checks that committed
contracts match the current circuit, configuration, proof inputs and templates.
