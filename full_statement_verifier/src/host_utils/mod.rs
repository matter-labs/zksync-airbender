pub mod cost_model;
pub mod fixture_artifact;
pub mod fixture_codec;
mod fsv;
#[cfg(test)]
mod reduced_isa_gate;

pub use fsv::{canonical_fsv_dir, fsv_digest, load_fsv_exact, FsvDigest, VerifiedFsvProgram};

use crate::program_proof::ProgramProof;
use crate::recursion_chain::{self, RecursionChain};
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};
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

/// The ND stream the guest of `descriptor` reads for `proof`: the unrolled layers verify an
/// unrolled proof, the unified layers a unified one, flattened for `descriptor.blake`.
pub fn fsv_stream(setups: &Setups, proof: &ProgramProof, descriptor: &FsvDescriptor) -> Vec<u32> {
    match descriptor.program {
        FsvProgram::UnrolledBaseLayer | FsvProgram::UnrolledRecursionLayer => {
            build_unrolled_stream(setups, proof, descriptor.blake)
        }
        FsvProgram::UnifiedBaseLayer | FsvProgram::UnifiedRecursionLayer => {
            build_unified_stream(setups, proof, descriptor.blake)
        }
    }
}

fn flattened_caps(setups: &Setups) -> impl Iterator<Item = &[u32]> {
    setups.values().map(|params| params.flattened_setup_caps())
}

#[cfg(feature = "verifiers")]
fn run_native_verifier(
    name: &str,
    verify: impl FnOnce() -> Result<[u32; 16], String> + Send + 'static,
) -> Result<[u32; 16], String> {
    std::thread::Builder::new()
        .name(name.to_owned())
        .stack_size(1 << 27)
        .spawn(verify)
        .map_err(|error| format!("cannot start native verifier: {error}"))?
        .join()
        .map_err(|_| "native verifier rejected input with a panic".to_owned())?
}

/// Verify under the caller-selected schedule, returning malformed/invalid proof errors.
#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> Result<[u32; 16], String> {
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

/// Native verification of an compression stream (the zero-delegation
/// compression statement) at a checked boundary: a verifier error, a structural
/// panic inside the statement (a nonzero delegation count, a truncated
/// stream), or trailing words after the statement consumed its input are all
/// reported as `Err`.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified_compression_final(stream: Vec<u32>) -> Result<[u32; 16], String> {
    let joined = std::thread::Builder::new()
        .name("unified l1 compression verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut it = stream.into_iter();
            let output = crate::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_compression_final::<
                _, verifier_common::errors::DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS,
            >(&mut it)
                .map_err(|err| format!("unified l1 compression proof failed to verify: {err:?}"))?;
            let trailing = it.count();
            if trailing != 0 {
                return Err(format!(
                    "unified l1 compression stream carries {trailing} trailing words after the statement"
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
                "unified l1 compression statement rejected the stream: {reason}"
            ))
        }
    }
}

/// Verify under the caller-selected schedule, returning malformed/invalid proof errors.
#[cfg(feature = "verifiers")]
pub fn native_verify_unified_in_mode(
    stream: Vec<u32>,
    is_base: bool,
    mode: SoundnessMode,
) -> Result<[u32; 16], String> {
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

fn blake_mode_from_env(vars: &[&str], default: BlakeMode) -> BlakeMode {
    for var in vars {
        if let Ok(v) = std::env::var(var) {
            let mode = BlakeMode::parse(&v).unwrap_or_else(|| panic!("invalid {var}={v}"));
            return mode;
        }
    }
    default
}

#[must_use]
pub fn unrolled_blake_mode() -> BlakeMode {
    blake_mode_from_env(&["RECURSION_UNROLLED_BLAKE"], BlakeMode::Compression)
}

#[must_use]
pub fn bridge_blake_mode() -> BlakeMode {
    blake_mode_from_env(&["RECURSION_BRIDGE_BLAKE"], unrolled_blake_mode())
}

#[must_use]
pub fn final_blake_mode() -> BlakeMode {
    blake_mode_from_env(
        &["RECURSION_FINAL_BLAKE", "RECURSION_UNIFIED_BLAKE"],
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
/// Rounded heavy-block calibration for the Sec100 verifier, shared by every soundness mode.
/// Circuit-count boundaries make the crossover workload-dependent.
pub const DEFAULT_UNIFIED_SWITCH_CYCLES: u64 = 52_000_000;

/// Lower bound on the switch threshold to ensure unrolled recursion can converge.
pub const MIN_UNIFIED_SWITCH_CYCLES: u64 = 16 * 1024 * 1024;

/// Override the number of unrolled layers proved in one pipeline invocation.
#[must_use]
pub fn recursion_unrolled_layers() -> Option<usize> {
    std::env::var_os("RECURSION_UNROLLED_LAYERS").map(|value| {
        value
            .to_str()
            .expect("RECURSION_UNROLLED_LAYERS must be a usize")
            .parse()
            .expect("RECURSION_UNROLLED_LAYERS must be a usize")
    })
}

#[must_use]
pub fn unified_switch_cycles() -> u64 {
    let cycles = std::env::var("RECURSION_UNIFIED_SWITCH_CYCLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_UNIFIED_SWITCH_CYCLES);
    assert!(
        cycles >= MIN_UNIFIED_SWITCH_CYCLES,
        "unified switch threshold {cycles} is below the convergence floor \
         {MIN_UNIFIED_SWITCH_CYCLES}; lower thresholds may never stop unrolled recursion"
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
                assert!(native_verify_unrolled_in_mode(Vec::new(), is_base, mode).is_err());
                assert!(native_verify_unified_in_mode(Vec::new(), is_base, mode).is_err());
            }
        }
    }
}
