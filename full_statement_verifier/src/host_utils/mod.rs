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

/// Failure of a mode-explicit native verifier. Invalid input never selects another mode.
#[cfg(feature = "verifiers")]
#[derive(Debug)]
pub enum NativeVerificationError {
    Spawn(std::io::Error),
    InvalidProof(String),
    ThreadPanicked,
}

#[cfg(feature = "verifiers")]
impl std::fmt::Display for NativeVerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Spawn(error) => write!(f, "cannot start native verifier: {error}"),
            Self::InvalidProof(error) => write!(f, "invalid proof: {error}"),
            Self::ThreadPanicked => write!(f, "native verifier rejected input with a panic"),
        }
    }
}

#[cfg(feature = "verifiers")]
impl std::error::Error for NativeVerificationError {}

#[cfg(feature = "verifiers")]
fn run_native_verifier(
    name: &str,
    verify: impl FnOnce() -> Result<[u32; 16], String> + Send + 'static,
) -> Result<[u32; 16], NativeVerificationError> {
    std::thread::Builder::new()
        .name(name.to_owned())
        .stack_size(1 << 27)
        .spawn(verify)
        .map_err(NativeVerificationError::Spawn)?
        .join()
        .map_err(|_| NativeVerificationError::ThreadPanicked)?
        .map_err(NativeVerificationError::InvalidProof)
}

/// Pessimistic compatibility wrapper for a proof expected to be valid.
#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    native_verify_unrolled_in_mode(stream, is_base, SoundnessMode::PessimisticConjecture)
}

#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> [u32; 16] {
    try_native_verify_unrolled_in_mode(stream, is_base, mode).expect("unrolled proof must verify")
}

/// Verify under the caller-selected schedule, returning malformed/invalid proof errors.
#[cfg(feature = "verifiers")]
pub fn try_native_verify_unrolled_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> Result<[u32; 16], NativeVerificationError> {
    use verifier_common::errors::DebugErrorCreator;
    run_native_verifier("unrolled verifier", move || {
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
        result.map_err(|error| format!("{error:?}"))
    })
}

/// Pessimistic compatibility wrapper for a proof expected to be valid.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
    native_verify_unified_in_mode(stream, is_base, SoundnessMode::PessimisticConjecture)
}

#[cfg(feature = "verifiers")]
pub fn native_verify_unified_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> [u32; 16] {
    try_native_verify_unified_in_mode(stream, is_base, mode).expect("unified proof must verify")
}

/// Verify under the caller-selected schedule, returning malformed/invalid proof errors.
#[cfg(feature = "verifiers")]
pub fn try_native_verify_unified_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> Result<[u32; 16], NativeVerificationError> {
    use verifier_common::errors::DebugErrorCreator;
    run_native_verifier("unified verifier", move || {
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
        result.map_err(|error| format!("{error:?}"))
    })
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

#[cfg(all(test, feature = "verifiers"))]
mod native_mode_tests {
    use super::*;

    #[test]
    fn malformed_native_proofs_return_errors_in_each_mode() {
        for &mode in SoundnessMode::ALL {
            for is_base in [true, false] {
                assert!(try_native_verify_unrolled_in_mode(Vec::new(), is_base, mode).is_err());
                assert!(try_native_verify_unified_in_mode(Vec::new(), is_base, mode).is_err());
            }
        }
    }
}
