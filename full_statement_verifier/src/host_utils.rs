use crate::program_proof::ProgramProof;
use crate::recursion_chain::{self, RecursionChain};
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
use verifier_common::prover::definitions::MerkleTreeCap;
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

#[must_use]
pub fn build_unrolled_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    proof.build_unrolled_stream(flattened_caps(setups))
}

#[must_use]
pub fn build_unified_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    proof.build_unified_stream(flattened_caps(setups))
}

fn flattened_caps(setups: &Setups) -> impl Iterator<Item = &[u32]> {
    setups
        .values()
        .map(|params| MerkleTreeCap::flatten_single(&params.setup_caps))
}


#[cfg(feature = "verifiers")]
pub fn native_verify_unrolled(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
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
                >(&mut it)
            } else {
                crate::unrolled_proof_statement::verify_unrolled_recursion_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it)
            };
            result.expect("unrolled proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}

#[cfg(feature = "verifiers")]
pub fn native_verify_unified(stream: Vec<u32>, is_base: bool) -> [u32; 16] {
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
                >(&mut it)
            } else {
                crate::unified_circuit_statement::verify_unified_circuit_recursion_layer::<
                    _,
                    DebugErrorCreator,
                    USE_REDUCED_BLAKE2_ROUNDS,
                >(&mut it)
            };
            result.expect("unified proof must verify")
        })
        .expect("spawn verifier thread")
        .join()
        .expect("verifier thread must not panic")
}

#[must_use]
pub fn load_program(bin_path: &Path, text_path: &Path) -> (Vec<u32>, Vec<u32>) {
    let (_, binary_image) = setups::read_and_pad_binary(bin_path);
    let (_, text_section) = setups::read_and_pad_binary(text_path);
    (binary_image, text_section)
}

#[must_use]
pub fn load_fsv_program(
    dir: impl AsRef<Path>,
    program: FsvProgram,
    blake: BlakeMode,
) -> (Vec<u32>, Vec<u32>) {
    let dir = dir.as_ref();
    let stem = program.file_stem(blake);
    if dir.join(format!("{stem}.bin")).exists() {
        load_program(
            &dir.join(format!("{stem}.bin")),
            &dir.join(format!("{stem}.text")),
        )
    } else {
        assert!(
            blake == BlakeMode::Compression,
            "missing variant binary {} — run `cd tools/gkr_verifier && ./dump_recursive_verifiers.sh`",
            dir.join(format!("{stem}.bin")).display()
        );
        let base = program.base_name();
        load_program(
            &dir.join(format!("{base}.bin")),
            &dir.join(format!("{base}.text")),
        )
    }
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
/// Once a single verifier invocation runs in fewer cycles than this, it is
/// small enough to be proven on the unified machine (a few 1<<24 instances),
/// so unrolled recursion can stop and bridge to unified. A scheduling
/// heuristic, not a protocol constant — drivers may pick their own threshold.
pub const DEFAULT_UNIFIED_SWITCH_CYCLES: u64 = 64 * 1024 * 1024;

#[must_use]
pub fn unified_switch_cycles() -> u64 {
    std::env::var("RECURSION_UNIFIED_SWITCH_CYCLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_UNIFIED_SWITCH_CYCLES)
}
