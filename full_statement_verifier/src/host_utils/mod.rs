pub mod cost_model;
pub mod fixture_codec;
mod fsv;
mod fsv_execution;

pub use fsv::{
    canonical_fsv_dir, fsv_digest, fsv_manifest, fsv_manifest_entry, load_fsv_exact,
    load_fsv_program, render_fsv_manifest, FsvDigest, FsvLoadError, FsvManifestEntry,
    VerifiedFsvProgram, FSV_DIGEST_RECIPE, FSV_MANIFEST_FILE,
};
pub use fsv_execution::{
    append_fsv_ledger, fsv_ledger_row, fsv_stream, measure_fsv_blake_variants,
    measure_fsv_execution, FsvExecutionError, FsvExecutionFailure, FsvExecutionRecord,
    FSV_EXECUTION_CYCLES_LIMIT,
};

use crate::program_proof::ProgramProof;
use crate::recursion_chain::{self, RecursionChain};
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
use verifier_common::prover::definitions::MerkleTreeCap;
#[cfg(feature = "verifiers")]
use verifier_common::prover::definitions::{SecurityLevel, SoundnessMode};
use verifier_common::USE_REDUCED_BLAKE2_ROUNDS;

/// The recursion chain as hashed by the deployed fsv binaries.
pub type FsvRecursionChain = RecursionChain<USE_REDUCED_BLAKE2_ROUNDS>;

/// `end_params` of a program: `blake(final_pc_buffer || each setup cap)`, with
/// the deployed binaries' rounds variant.
#[must_use]
pub fn compute_end_params(setups: &Setups, final_pc: u32) -> [u32; 8] {
    recursion_chain::compute_end_params::<USE_REDUCED_BLAKE2_ROUNDS>(
        final_pc,
        flattened_caps(setups),
    )
}

/// The ND stream of an unrolled proof for a full-statement verifier built
/// with `blake` (the mode its guest was loaded for, or
/// `verifier_common::BLAKE_MODE` for the native verifier of this process).
#[must_use]
pub fn build_unrolled_stream(setups: &Setups, proof: &ProgramProof, blake: BlakeMode) -> Vec<u32> {
    proof.build_unrolled_stream(flattened_caps(setups), blake)
}

/// [`build_unrolled_stream`] of a unified proof.
#[must_use]
pub fn build_unified_stream(setups: &Setups, proof: &ProgramProof, blake: BlakeMode) -> Vec<u32> {
    proof.build_unified_stream(flattened_caps(setups), blake)
}

fn flattened_caps(setups: &Setups) -> impl Iterator<Item = &[u32]> {
    setups
        .values()
        .map(|params| MerkleTreeCap::flatten_single(&params.setup_caps))
}

/// [`native_verify_unrolled_in_mode`] in the default soundness mode.
#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    native_verify_unrolled_in_mode(stream, is_base, SoundnessMode::DEFAULT)
}

#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> [u32; 16] {
    use verifier_common::errors::DebugErrorCreator;
    std::thread::Builder::new()
        .name("unrolled verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let result = if is_base {
                crate::unrolled_proof_statement::verify_unrolled_base_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it, SecurityLevel::Sec100, mode)
            } else {
                crate::unrolled_proof_statement::verify_unrolled_recursion_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it, SecurityLevel::Sec100, mode)
            };
            result.expect("unrolled proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}

/// [`native_verify_unified_in_mode`] in the default soundness mode.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    native_verify_unified_in_mode(stream, is_base, SoundnessMode::DEFAULT)
}

#[cfg(feature = "verifiers")]
pub fn native_verify_unified_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> [u32; 16] {
    use verifier_common::errors::DebugErrorCreator;
    std::thread::Builder::new()
        .name("unified verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let result = if is_base {
                crate::unified_circuit_statement::verify_unified_circuit_base_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it, SecurityLevel::Sec100, mode)
            } else {
                crate::unified_circuit_statement::verify_unified_circuit_recursion_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it, SecurityLevel::Sec100, mode)
            };
            result.expect("unified proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}

/// Load a guest from its linked ELF (legacy read mode: `.text` followed in ROM by the
/// `.rodata`/`.data` init images): `(flat ROM image, text section)`, both padded to the ROM
/// size for proving.
#[must_use]
pub fn load_program(elf_path: &Path) -> (Vec<u32>, Vec<u32>) {
    riscv_transpiler::elf::load_legacy_program(elf_path)
}

fn blake_mode_from_env(vars: &[&str], program: FsvProgram, default: BlakeMode) -> BlakeMode {
    for var in vars {
        if let Ok(v) = std::env::var(var) {
            let mode = BlakeMode::parse(&v).unwrap_or_else(|| panic!("invalid {var}={v}"));
            assert!(
                program.supports(mode),
                "{var}={v}: {} is not built with this blake mode",
                program.base_name()
            );
            return mode;
        }
    }
    default
}

#[must_use]
pub fn unrolled_blake_mode() -> BlakeMode {
    blake_mode_from_env(
        &["RECURSION_UNROLLED_BLAKE"],
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
    )
}

#[must_use]
pub fn bridge_blake_mode() -> BlakeMode {
    blake_mode_from_env(
        &["RECURSION_BRIDGE_BLAKE"],
        FsvProgram::UnrolledRecursionLayer,
        unrolled_blake_mode(),
    )
}

#[must_use]
pub fn final_blake_mode() -> BlakeMode {
    blake_mode_from_env(
        &["RECURSION_FINAL_BLAKE", "RECURSION_UNIFIED_BLAKE"],
        FsvProgram::UnifiedRecursionLayer,
        BlakeMode::Compression,
    )
}

/// Default for the unrolled-to-unified switch threshold.
///
/// Unrolled recursion stops once the *estimated* cycle count of the next
/// verifier invocation drops below this. A scheduling heuristic, not a
/// protocol constant — drivers may pick their own, and
/// `RECURSION_UNIFIED_SWITCH_CYCLES` overrides it.
///
/// Rounded heavy-block calibration for the Sec100 verifier.
/// Circuit-count boundaries make the crossover workload-dependent.
pub const DEFAULT_UNIFIED_SWITCH_CYCLES: u64 = 52_000_000;

/// The estimated verifier cost never drops below ~6.55M cycles (past the first
/// layer, each unrolled recursion layer verifies another such layer), so lower
/// thresholds never stop the unrolled recursion loop. 16Mi leaves
/// recalibration margin.
pub const MIN_UNIFIED_SWITCH_CYCLES: u64 = 16 * 1024 * 1024;

#[must_use]
pub fn unified_switch_cycles() -> u64 {
    let cycles = std::env::var("RECURSION_UNIFIED_SWITCH_CYCLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_UNIFIED_SWITCH_CYCLES);
    assert!(
        cycles >= MIN_UNIFIED_SWITCH_CYCLES,
        "unified switch threshold {cycles} is below the convergence floor \
         {MIN_UNIFIED_SWITCH_CYCLES}: the estimated verifier cost never drops \
         below ~6.55M cycles, so lower thresholds never stop the unrolled \
         recursion loop"
    );
    cycles
}
