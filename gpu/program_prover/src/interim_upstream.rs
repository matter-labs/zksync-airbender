//! TEMPORARY mirrors of the recursion-protocol helpers that currently live in
//! `prover_examples::recursion` — a `#[cfg(test)]` module in an examples
//! crate, so not importable as library code. Upstream has been asked
//! (2026-07-03) to move these into `full_statement_verifier` / `setups`;
//! delete this module and re-point callers through `crate::upstream` once
//! that lands. Keep the bodies byte-equivalent to the upstream originals
//! (`circuit_defs/prover_examples/src/recursion.rs`) — any drift here breaks
//! the recursion hash chain or the ND stream contract silently.

use std::collections::BTreeMap;

use crate::upstream::{
    Blake2sBufferingTranscript, MerkleTreeCap, ProgramProof, UnrolledCircuitSetupParams,
    INITIAL_TIMESTAMP, TIMESTAMP_STEP,
};

/// Mirrors `recursion.rs::REDUCED_ROUNDS`: the whole GKR stack runs on
/// reduced-round blake2s transcripts.
pub const REDUCED_ROUNDS: bool = true;

/// Mirrors `recursion.rs::UNIFIED_SWITCH_CYCLES`: proofs at or below this
/// cycle count bridge from the unrolled recursion loop to the unified circuit.
pub const UNIFIED_SWITCH_CYCLES: u64 = 64 * 1024 * 1024;

/// Per-program setup-params map, keyed by circuit family index. The value
/// order (BTreeMap ascending) defines the setup-cap order in the ND streams
/// and in `compute_end_params`.
pub type Setups = BTreeMap<u32, UnrolledCircuitSetupParams>;

/// Hash of (final pc, all setup caps) — the verifier's `end_params_output`.
pub fn compute_end_params(setups: &Setups, final_pc: u32) -> [u32; 8] {
    let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
    let mut buffer = [0u32; 16];
    buffer[0] = final_pc;
    hasher.absorb(&buffer);
    for params in setups.values() {
        hasher.absorb(MerkleTreeCap::flatten_single(&params.setup_caps));
    }
    hasher.finalize_reset().0
}

/// Start the recursion hash chain from the base program's end params.
pub fn begin_chain(base_end_params: &[u32; 8]) -> ([u32; 8], [u32; 16]) {
    let mut preimage = [0u32; 16];
    preimage[8..].copy_from_slice(base_end_params);
    let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
    hasher.absorb(&preimage);
    let hash = hasher.finalize_reset().0;
    (hash, preimage)
}

/// Extend the recursion hash chain — including the "same program again →
/// don't re-commit" rule.
pub fn continue_chain(
    prev_hash: &[u32; 8],
    prev_preimage: &[u32; 16],
    end_params: &[u32; 8],
) -> ([u32; 8], [u32; 16]) {
    if &prev_preimage[8..] == &end_params[..] {
        (*prev_hash, *prev_preimage)
    } else {
        let mut preimage = [0u32; 16];
        preimage[..8].copy_from_slice(prev_hash);
        preimage[8..].copy_from_slice(end_params);
        let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
        hasher.absorb(&preimage);
        let hash = hasher.finalize_reset().0;
        (hash, preimage)
    }
}

/// ND stream for the unrolled verifiers: setup caps followed by the flattened
/// proof.
pub fn build_unrolled_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    let mut stream: Vec<u32> = setups
        .values()
        .flat_map(|p| MerkleTreeCap::flatten_single(&p.setup_caps).to_vec())
        .collect();
    stream.extend(proof.flatten_for_verification());
    stream
}

/// ND stream for the unified verifier: setup caps followed by the flattened
/// unified proof.
pub fn build_unified_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    let mut stream: Vec<u32> = setups
        .values()
        .flat_map(|p| MerkleTreeCap::flatten_single(&p.setup_caps).to_vec())
        .collect();
    stream.extend(proof.flatten_unified_for_verification());
    stream
}

/// Executed cycle count implied by a proof's final timestamp.
pub fn proof_cycles(proof: &ProgramProof) -> u64 {
    (proof.final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
}

/// Native (host) verification of an unrolled-layer stream. Runs on its own
/// thread with a large stack — the verifiers recurse deeply.
#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    use crate::upstream::{
        verify_unrolled_base_layer, verify_unrolled_recursion_layer, DebugErrorCreator,
    };
    std::thread::Builder::new()
        .name("unrolled verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let result = if is_base {
                verify_unrolled_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut it)
            } else {
                verify_unrolled_recursion_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut it)
            };
            result.expect("unrolled proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}

/// Native (host) verification of a unified-layer stream. Extends the upstream
/// mirror with an `is_base` switch: the base variant starts a fresh recursion
/// chain (requires the upper 8 output registers to be zero, reads no chain
/// preimage), matching proofs of ordinary programs rather than fsv binaries.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    use crate::upstream::{
        verify_unified_circuit_base_layer, verify_unified_circuit_recursion_layer,
        DebugErrorCreator,
    };
    std::thread::Builder::new()
        .name("unified verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let result = if is_base {
                verify_unified_circuit_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut it)
            } else {
                verify_unified_circuit_recursion_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(
                    &mut it,
                )
            };
            result.expect("unified proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}
