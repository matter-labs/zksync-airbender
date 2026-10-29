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
    append_fsv_ledger, fsv_ledger_row, fsv_stream, fsv_stream_digest, measure_fsv_blake_variants,
    measure_fsv_execution, FsvExecutionError, FsvExecutionFailure, FsvExecutionRecord,
    FSV_EXECUTION_CYCLES_LIMIT,
};

use crate::program_proof::ProgramProof;
use crate::recursion_chain::{self, RecursionChain};
use riscv_transpiler::elf::{read_elf_from_path_with_rom, ElfImage, ElfReadError, ElfReadMode};
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
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
    setups.values().map(|params| params.flattened_setup_caps())
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


/// Native verification of an L1 feeder stream (the zero-delegation
/// feeder statement) at a checked boundary: a verifier error, a structural
/// panic inside the statement (a nonzero delegation count, a truncated
/// stream), or trailing words after the statement consumed its input are all
/// reported as `Err`.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified_l1_feeder(stream: Vec<u32>) -> Result<[u32; 16], String> {
    native_verify_l1_feeder_statement(
        stream,
        crate::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_l1_feeder::<
            _,
            verifier_common::errors::DebugErrorCreator,
            USE_REDUCED_BLAKE2_ROUNDS,
        >,
    )
}

/// [`native_verify_unified_l1_feeder`] over a proof of the 2^23 feeder
/// profile A.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified_l1_feeder_a(stream: Vec<u32>) -> Result<[u32; 16], String> {
    native_verify_l1_feeder_statement(
        stream,
        crate::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_l1_feeder_a::<
            _,
            verifier_common::errors::DebugErrorCreator,
            USE_REDUCED_BLAKE2_ROUNDS,
        >,
    )
}

#[cfg(feature = "verifiers")]
fn native_verify_l1_feeder_statement(
    stream: Vec<u32>,
    statement: fn(
        &mut std::vec::IntoIter<u32>,
    ) -> Result<[u32; 16], verifier_common::errors::VerificationError>,
) -> Result<[u32; 16], String> {
    let joined = std::thread::Builder::new()
        .name("unified l1 feeder verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let output = statement(&mut it)
                .map_err(|err| format!("unified l1 feeder proof failed to verify: {err:?}"))?;
            let trailing = it.count();
            if trailing != 0 {
                return Err(format!(
                    "unified l1 feeder stream carries {trailing} trailing words after the statement"
                ));
            }
            Ok(output)
        })
        .expect("spawn verifier thread")
        .join();
    match joined {
        Ok(result) => result,
        Err(payload) => {
            let reason = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied())
                .unwrap_or("unknown verifier panic");
            Err(format!(
                "unified l1 feeder statement rejected the stream: {reason}"
            ))
        }
    }
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

/// Read the selected FSV ELF with its circuit-owned ROM geometry.
pub fn read_fsv_image(
    dir: impl AsRef<Path>,
    program: FsvProgram,
    blake: BlakeMode,
) -> Result<ElfImage, ElfReadError> {
    let dir = dir.as_ref();
    let stem = program.file_stem(blake);
    println!("Trying to load `{}` verifier", stem);
    let elf_path = dir.join(format!("{stem}.elf"));
    let exists = match elf_path.try_exists() {
        Ok(res) => res,
        Err(err) => {
            if let Some(err) = err.get_ref() {
                println!("Failed to probe path `{}`: {}", elf_path.display(), err);
            } else {
                println!("Failed to probe path `{}`", elf_path.display());
            }
            false
        }
    };
    let selected = if exists {
        elf_path
    } else {
        println!(
            "Verifier binary `{stem}` is absent at {}, using fallback naming mode",
            elf_path.display()
        );
        assert!(blake == BlakeMode::Compression,
            "missing variant binary {} — run `cd tools/gkr_verifier && ./dump_recursive_verifiers.sh`", elf_path.display());
        dir.join(format!("{}.elf", program.base_name()))
    };
    read_elf_from_path_with_rom(&selected, ElfReadMode::Legacy, program.rom())
}

/// C1's geometry-aware loader of an L1 guest (feeder A or wrap): the unpadded ROM image and
/// text. These guests are not registry rows yet, so the bytes are unpinned; the standard
/// guests load through [`load_fsv_exact`].
#[must_use]
pub fn load_l1_fsv_program(
    dir: impl AsRef<Path>,
    program: FsvProgram,
    blake: BlakeMode,
) -> (Vec<u32>, Vec<u32>) {
    assert!(
        matches!(
            program,
            FsvProgram::UnifiedRecursionLayerL1FeederA
                | FsvProgram::UnifiedRecursionLayerL1FeederWrap
        ),
        "{program:?} is a registry guest; load it with load_fsv_exact"
    );
    let image = read_fsv_image(dir, program, blake)
        .unwrap_or_else(|error| panic!("failed to load FSV {}: {error}", program.file_stem(blake)));
    let bin = image
        .objcopy_binary_words()
        .expect("legacy FSV image has a ROM image")
        .to_vec();
    let text = image.text;
    assert!(
        bin.len() <= program.rom().word_size(),
        "FSV image exceeds selected ROM"
    );
    assert!(
        text.len() <= program.rom().word_size(),
        "FSV text exceeds selected ROM"
    );
    (bin, text)
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
