//! Execution of digest-verified full-statement verifier guests in the RISC-V interpreter: the
//! cycle count a recursion layer will prove, the verifier's returned words, and ledger rows
//! that record both per guest.
//!
//! [`measure_fsv_execution`] runs the interpreter procedure of the recursion examples
//! (`program_prover::unrolled::run_unrolled_machine_in_full` on the reduced machine) over the
//! exact words [`load_fsv_exact`](super::load_fsv_exact) verified, without recording snapshots.

use super::{
    build_unified_stream, build_unrolled_stream, load_fsv_exact, FsvDigest, FsvLoadError,
    VerifiedFsvProgram,
};
use crate::program_proof::ProgramProof;
use common_constants::{INITIAL_TIMESTAMP, ROM_SECOND_WORD_BITS, TIMESTAMP_STEP};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::{MachineConfig, ReducedMachineWithDelegation};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::vm::{
    DelegationsAndUnifiedCounters, RamWithRomRegion, SimpleTape, State, VM,
};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::fmt;
use std::path::Path;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::fsv_binaries::{
    BlakeMode, FsvDescriptor, FsvProfile, FsvProgram, SecurityLevel, SoundnessMode,
    UnsupportedFsvVariant, FSV_REGISTRY,
};

/// The most cycles one guest execution may take: the 32-bit timestamp bound
/// (`4 * cycles + 4 <= u32::MAX`, as `prover_pipeline::MAX_EXECUTION_CYCLES`).
pub const FSV_EXECUTION_CYCLES_LIMIT: usize = (u32::MAX as usize - 4) / 4;

/// RAM of the interpreter run, as in the recursion examples.
const RAM_BOUND: usize = 1 << 30;

/// A guest execution that reached the program's exit loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FsvExecutionRecord {
    pub descriptor: FsvDescriptor,
    /// The pinned digest the executed words were verified against.
    pub digest: FsvDigest,
    pub cycles: u64,
    /// `x10..x25` at the exit loop: the words the verifier returned.
    pub output: [u32; 16],
    /// Length of the ND stream the guest was given.
    pub stream_words: usize,
    /// [`fsv_stream_digest`] of that stream: which input was executed.
    pub stream_digest: FsvDigest,
}

/// A guest execution that did not reach the program's exit loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FsvExecutionError {
    pub descriptor: FsvDescriptor,
    pub digest: FsvDigest,
    pub stream_words: usize,
    pub stream_digest: FsvDigest,
    pub failure: FsvExecutionFailure,
}

/// Keccak256 of `le_u64(stream.len()) || stream words` (length in words, words
/// little-endian): the identity of an ND stream in execution records and ledger rows.
#[must_use]
pub fn fsv_stream_digest(stream: &[u32]) -> FsvDigest {
    let mut hasher = Keccak256::new();
    hasher.update((stream.len() as u64).to_le_bytes());
    for word in stream {
        hasher.update(word.to_le_bytes());
    }
    FsvDigest(hasher.finalize().into())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FsvExecutionFailure {
    /// The image does not hold `riscv_common::EXIT_SEQUENCE` exactly once.
    NoExitPoint,
    /// No terminal self-loop within `limit` cycles.
    CycleLimit { limit: usize },
    /// Terminated in a self-loop that is not the exit loop.
    WrongTerminal { pc: u32, exit_pc: u32, cycles: u64 },
    /// The interpreter aborted: the verifier's failure exit (`zksync_os_finish_error`, an
    /// illegal instruction to the interpreter), an exhausted ND stream, or any other illegal
    /// instruction. `message` is the interpreter's panic message.
    Aborted { message: String },
}

impl fmt::Display for FsvExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            descriptor,
            digest,
            stream_words,
            stream_digest,
            failure,
        } = self;
        write!(
            f,
            "full-statement verifier {descriptor} (digest {digest}) on a {stream_words}-word \
             stream (digest {stream_digest}) did not return: "
        )?;
        match failure {
            FsvExecutionFailure::NoExitPoint => {
                write!(f, "the image has no unique exit sequence")
            }
            FsvExecutionFailure::CycleLimit { limit } => {
                write!(f, "no terminal loop within {limit} cycles")
            }
            FsvExecutionFailure::WrongTerminal {
                pc,
                exit_pc,
                cycles,
            } => write!(
                f,
                "stopped in the loop at pc 0x{pc:08x} after {cycles} cycles, not at the exit \
                 loop 0x{exit_pc:08x}"
            ),
            FsvExecutionFailure::Aborted { message } => {
                write!(f, "the interpreter aborted: {message}")
            }
        }
    }
}

impl std::error::Error for FsvExecutionError {}

/// Execute `program` on `stream`, the ND stream the recursion layer will prove, and return
/// the cycles and the verifier's returned words. Succeeds only if the run ends in the
/// program's exit loop; comparing the output against an expected chain is the caller's.
pub fn measure_fsv_execution(
    program: &VerifiedFsvProgram,
    stream: Vec<u32>,
) -> Result<FsvExecutionRecord, FsvExecutionError> {
    execute(
        *program.descriptor(),
        program.digest(),
        program.bin(),
        program.text(),
        stream,
        FSV_EXECUTION_CYCLES_LIMIT,
    )
}

fn execute(
    descriptor: FsvDescriptor,
    digest: FsvDigest,
    bin: &[u32],
    text: &[u32],
    stream: Vec<u32>,
    cycles_limit: usize,
) -> Result<FsvExecutionRecord, FsvExecutionError> {
    let stream_words = stream.len();
    let stream_digest = fsv_stream_digest(&stream);
    let fail = |failure| FsvExecutionError {
        descriptor,
        digest,
        stream_words,
        stream_digest,
        failure,
    };
    let exit_pc = std::panic::catch_unwind(|| setups::program_setups::find_binary_exit_point(bin))
        .map_err(|_| fail(FsvExecutionFailure::NoExitPoint))?;

    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let instructions: Vec<Instruction> = preprocess_bytecode::<
            <ReducedMachineWithDelegation as MachineConfig>::DecodingOptions,
            true,
        >(text);
        let tape = SimpleTape::new(&instructions);
        let mut ram =
            RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(bin, RAM_BOUND);
        let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
        let finished =
            VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
                &mut state,
                &mut ram,
                &mut (),
                &tape,
                cycles_limit,
                &mut QuasiUARTSource::new_with_reads(stream),
            );
        let output: [u32; 16] = std::array::from_fn(|i| state.registers[10 + i].value);
        (finished, state.pc, state.timestamp, output)
    }));
    let (finished, pc, timestamp, output) = run.map_err(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
            .unwrap_or_else(|| "non-string panic payload".to_owned());
        fail(FsvExecutionFailure::Aborted { message })
    })?;
    let cycles = (timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    if !finished {
        return Err(fail(FsvExecutionFailure::CycleLimit {
            limit: cycles_limit,
        }));
    }
    if pc != exit_pc {
        return Err(fail(FsvExecutionFailure::WrongTerminal {
            pc,
            exit_pc,
            cycles,
        }));
    }
    Ok(FsvExecutionRecord {
        descriptor,
        digest,
        cycles,
        output,
        stream_words,
        stream_digest,
    })
}

/// The ND stream the guest of `descriptor` reads for `proof`: the unrolled layers verify an
/// unrolled proof, the unified layers a unified one, flattened for `descriptor.blake`.
pub fn fsv_stream(
    setups: &Setups,
    proof: &ProgramProof,
    descriptor: &FsvDescriptor,
) -> Result<Vec<u32>, UnsupportedFsvVariant> {
    descriptor.registry_entry()?;
    Ok(match descriptor.program {
        FsvProgram::UnrolledBaseLayer | FsvProgram::UnrolledRecursionLayer => {
            build_unrolled_stream(setups, proof, descriptor.blake)
        }
        FsvProgram::UnifiedBaseLayer
        | FsvProgram::UnifiedRecursionLayer
        | FsvProgram::UnifiedRecursionLayerL1FeederWrap
        | FsvProgram::UnifiedRecursionLayerL1FeederA => {
            build_unified_stream(setups, proof, descriptor.blake)
        }
    })
}

/// Load and execute every built blake variant of the standard-profile `program` for
/// `(security, soundness_mode)` on `proof`, in registry order: compression and special
/// opcodes for the unified recursion layer, compression for the others. A program with no
/// built variant is [`FsvLoadError::Unsupported`].
pub fn measure_fsv_blake_variants(
    dir: impl AsRef<Path>,
    security: SecurityLevel,
    soundness_mode: SoundnessMode,
    program: FsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
) -> Result<Vec<Result<FsvExecutionRecord, FsvExecutionError>>, FsvLoadError> {
    let descriptors: Vec<FsvDescriptor> = FSV_REGISTRY
        .iter()
        .map(|entry| entry.descriptor)
        .filter(|descriptor| {
            descriptor.security == security
                && descriptor.soundness_mode == soundness_mode
                && descriptor.program == program
                && descriptor.profile == FsvProfile::Standard
        })
        .collect();
    if descriptors.is_empty() {
        let compression =
            FsvDescriptor::new(security, soundness_mode, program, BlakeMode::Compression);
        return Err(FsvLoadError::Unsupported(
            compression
                .registry_entry()
                .expect_err("no standard-profile variant of the program is built"),
        ));
    }
    descriptors
        .into_iter()
        .map(|descriptor| {
            let guest = load_fsv_exact(dir.as_ref(), &descriptor)?;
            let stream =
                fsv_stream(setups, proof, &descriptor).map_err(FsvLoadError::Unsupported)?;
            Ok(measure_fsv_execution(&guest, stream))
        })
        .collect()
}

/// One execution-ledger row: the full descriptor, the pinned digest, success, cycles (when
/// known), the stream length and digest, and the returned words or the failure.
#[must_use]
pub fn fsv_ledger_row(
    label: &str,
    result: &Result<FsvExecutionRecord, FsvExecutionError>,
) -> serde_json::Value {
    let (descriptor, digest, stream_words, stream_digest) = match result {
        Ok(record) => (
            record.descriptor,
            record.digest,
            record.stream_words,
            record.stream_digest,
        ),
        Err(error) => (
            error.descriptor,
            error.digest,
            error.stream_words,
            error.stream_digest,
        ),
    };
    let [security, soundness_mode, program, profile, blake] = descriptor.tokens();
    let mut row = serde_json::json!({
        "label": label,
        "security": security,
        "soundness_mode": soundness_mode,
        "program": program,
        "profile": profile,
        "blake": blake,
        "digest": digest.to_string(),
        "success": result.is_ok(),
        "stream_words": stream_words,
        "stream_digest": stream_digest.to_string(),
    });
    let fields = row.as_object_mut().expect("a JSON object");
    match result {
        Ok(record) => {
            fields.insert("cycles".into(), record.cycles.into());
            let output: Vec<String> = record.output.iter().map(|w| format!("{w:08x}")).collect();
            fields.insert("output".into(), output.into());
        }
        Err(error) => {
            if let FsvExecutionFailure::WrongTerminal { cycles, .. } = error.failure {
                fields.insert("cycles".into(), cycles.into());
            }
            fields.insert("failure".into(), error.to_string().into());
        }
    }
    row
}

/// Append [`fsv_ledger_row`] to the JSON Lines file at `path`, creating it if needed.
pub fn append_fsv_ledger(
    path: &Path,
    label: &str,
    result: &Result<FsvExecutionRecord, FsvExecutionError>,
) -> std::io::Result<()> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;
    writeln!(file, "{}", fsv_ledger_row(label, result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host_utils::canonical_fsv_dir;
    use common_constants::ROM_WORD_SIZE;

    /// `riscv_common::EXIT_SEQUENCE` (not a dependency of this crate): sixteen
    /// `lw x10..x25, k(s10)` and the final self-loop. A drift makes these tests fail with
    /// `NoExitPoint`.
    const EXIT_SEQUENCE: &[u32] = &[
        0x000d2503, 0x004d2583, 0x008d2603, 0x00cd2683, 0x010d2703, 0x014d2783, 0x018d2803,
        0x01cd2883, 0x020d2903, 0x024d2983, 0x028d2a03, 0x02cd2a83, 0x030d2b03, 0x034d2b83,
        0x038d2c03, 0x03cd2c83, 0x0000006f,
    ];

    const SELF_LOOP: u32 = 0x0000_006f; // jal x0, 0
    const JUMP_FORWARD: u32 = 0x0040_006f; // jal x0, 4
    const JUMP_BACK: u32 = 0xffdf_f06f; // jal x0, -4
    const ERROR_EXIT: u32 = 0xc000_1073; // csrrw x0, cycle, x0: zksync_os_finish_error

    fn descriptor(mode: SoundnessMode, program: FsvProgram, blake: BlakeMode) -> FsvDescriptor {
        FsvDescriptor::new(SecurityLevel::Sec100, mode, program, blake)
    }

    /// Run `code` as both the ROM image and the text section, padded like a loaded guest.
    fn run(code: &[u32], limit: usize) -> Result<FsvExecutionRecord, FsvExecutionError> {
        let mut words = code.to_vec();
        words.resize(ROM_WORD_SIZE, 0);
        execute(
            descriptor(
                SoundnessMode::PessimisticConjecture,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::Compression,
            ),
            FsvDigest([0; 32]),
            &words,
            &words,
            vec![7, 8, 9],
            limit,
        )
    }

    fn with_exit(prefix: &[u32]) -> Vec<u32> {
        prefix.iter().chain(EXIT_SEQUENCE).copied().collect()
    }

    #[test]
    fn stream_digest_binds_length_and_words() {
        assert_ne!(fsv_stream_digest(&[1, 2]), fsv_stream_digest(&[2, 1]));
        assert_ne!(fsv_stream_digest(&[]), fsv_stream_digest(&[0]));
    }

    #[test]
    fn exit_loop_is_success_with_the_returned_words() {
        let record = run(EXIT_SEQUENCE, 1_000).unwrap();
        // s10 is 0, so the sixteen loads return the first sixteen words of the image.
        assert_eq!(record.output[..], EXIT_SEQUENCE[..16]);
        assert_eq!(record.cycles, EXIT_SEQUENCE.len() as u64);
        assert_eq!(record.stream_words, 3);
        assert_eq!(record.stream_digest, fsv_stream_digest(&[7, 8, 9]));
    }

    #[test]
    fn other_self_loop_is_wrong_terminal() {
        let err = run(&with_exit(&[SELF_LOOP]), 1_000).unwrap_err();
        assert_eq!(
            err.failure,
            FsvExecutionFailure::WrongTerminal {
                pc: 0,
                exit_pc: (EXIT_SEQUENCE.len() as u32) * 4,
                cycles: 1,
            }
        );
    }

    #[test]
    fn non_terminating_run_hits_the_cycle_limit() {
        let err = run(&with_exit(&[JUMP_FORWARD, JUMP_BACK]), 1_000).unwrap_err();
        assert_eq!(
            err.failure,
            FsvExecutionFailure::CycleLimit { limit: 1_000 }
        );
    }

    #[test]
    fn verifier_error_exit_is_an_abort() {
        let err = run(&with_exit(&[ERROR_EXIT]), 1_000).unwrap_err();
        match err.failure {
            FsvExecutionFailure::Aborted { message } => {
                assert!(message.contains("0x00000000"), "{message}")
            }
            other => panic!("expected Aborted, got {other:?}"),
        }
    }

    #[test]
    fn image_without_exit_sequence_is_rejected() {
        let err = run(&[SELF_LOOP], 1_000).unwrap_err();
        assert_eq!(err.failure, FsvExecutionFailure::NoExitPoint);
    }

    /// No ethproofs guest returns on a stream that is not a proof.
    #[test]
    fn ethproofs_guests_reject_a_garbage_stream() {
        for entry in FSV_REGISTRY {
            if entry.descriptor.soundness_mode != SoundnessMode::EthproofsSoundnessCalc {
                continue;
            }
            let guest = load_fsv_exact(canonical_fsv_dir(), &entry.descriptor).unwrap();
            let err = measure_fsv_execution(&guest, vec![0x5555_5555; 4096]).unwrap_err();
            assert!(
                matches!(
                    err.failure,
                    FsvExecutionFailure::Aborted { .. } | FsvExecutionFailure::WrongTerminal { .. }
                ),
                "{err}"
            );
            assert_eq!(err.digest, guest.digest());
        }
    }

    #[test]
    fn unbuilt_programs_are_unsupported_not_empty() {
        let ethproofs = SoundnessMode::EthproofsSoundnessCalc;
        let unified_base = descriptor(
            ethproofs,
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        );
        let empty: std::collections::BTreeMap<_, _> = Default::default();
        let proof = crate::program_proof::ProgramProof {
            riscv_proofs: empty.clone(),
            compiled_riscv_circuits: Default::default(),
            inits_and_teardown_proofs: vec![],
            inits_and_teardowns_circuit: None,
            delegation_proofs: empty,
            compiled_delegation_circuits: Default::default(),
            register_final_values: vec![],
            final_pc: 0,
            final_timestamp: 0,
            end_params: [0; 8],
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
            pow_challenge: 0,
            num_it_circuits: None,
        };
        let setups = Setups::default();
        assert_eq!(
            fsv_stream(&setups, &proof, &unified_base)
                .unwrap_err()
                .descriptor,
            unified_base
        );
        match measure_fsv_blake_variants(
            canonical_fsv_dir(),
            SecurityLevel::Sec100,
            ethproofs,
            FsvProgram::UnifiedBaseLayer,
            &setups,
            &proof,
        ) {
            Err(FsvLoadError::Unsupported(err)) => assert_eq!(err.descriptor, unified_base),
            other => panic!("expected Unsupported, got {other:?}"),
        }
    }

    #[test]
    fn ledger_rows_carry_the_descriptor_digest_and_outcome() {
        let ok = run(EXIT_SEQUENCE, 1_000);
        let err = run(&with_exit(&[SELF_LOOP]), 1_000);
        let ok_row = fsv_ledger_row("ok", &ok);
        assert_eq!(ok_row["soundness_mode"], "pessimistic_conjecture");
        assert_eq!(ok_row["program"], "unified_recursion_layer");
        assert_eq!(ok_row["profile"], "standard");
        assert_eq!(ok_row["blake"], "blake2_with_compression");
        assert_eq!(ok_row["security"], "sec_100");
        assert_eq!(ok_row["digest"], "00".repeat(32));
        assert_eq!(ok_row["success"], true);
        assert_eq!(ok_row["cycles"], EXIT_SEQUENCE.len() as u64);
        assert_eq!(ok_row["stream_words"], 3);
        assert_eq!(
            ok_row["stream_digest"],
            fsv_stream_digest(&[7, 8, 9]).to_string()
        );
        assert_eq!(ok_row["output"][0], format!("{:08x}", EXIT_SEQUENCE[0]));
        let err_row = fsv_ledger_row("err", &err);
        assert_eq!(err_row["success"], false);
        assert_eq!(err_row["stream_digest"], ok_row["stream_digest"]);
        assert_eq!(err_row["cycles"], 1);
        assert!(err_row["failure"]
            .as_str()
            .unwrap()
            .contains("not at the exit loop"));

        let path = std::env::temp_dir().join(format!("fsv-ledger-{}.jsonl", std::process::id()));
        let _ = std::fs::remove_file(&path);
        append_fsv_ledger(&path, "ok", &ok).unwrap();
        append_fsv_ledger(&path, "err", &err).unwrap();
        let lines: Vec<serde_json::Value> = std::fs::read_to_string(&path)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        let _ = std::fs::remove_file(&path);
        assert_eq!(lines, [ok_row, err_row]);
    }
}
