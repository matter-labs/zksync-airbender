//! The full L1 compression path: from the recursion pipeline's stable point
//! (ONE unified circuit proof + ONE blake precompile proof, standard schedule,
//! separate commitments) all the way down to the single Proth120 packed proof
//! the L1 EVM verifier consumes.
//!
//! Three stages, each proving a full-statement-verifier (fsv) RISC-V program
//! from `tools/gkr_verifier` in `MergedMemoryAndWitness` mode under the
//! high-LDE "L1 feeder" schedule (`l1_feeder_config_for_2_23`), following
//! `prover_examples`' `test_l1_feeder_high_lde_research`:
//!
//! 1. The STANDARD special-opcodes unified fsv
//!    (`fsv_unified_recursion_layer_sec_100_special_opcodes_extension`)
//!    verifies the input pair; proving that run takes THREE 2^23 feeder chunks.
//! 2. The MERGED-mode feeder fsv
//!    (`fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension`)
//!    verifies those three feeder proofs; proving it fits ONE feeder chunk.
//! 3. The same feeder fsv verifies that single proof in <= 2^22 cycles;
//!    proving THAT run with the EVM-production Proth120 packed parameters
//!    ([`crate::l1::prove_l1_wrap_in_memory`], all oracles in memory) yields
//!    the L1 proof.
//!
//! The recursion chain is resumed from the input proof's own
//! `recursion_chain_preimage` and threaded through the stages exactly like the
//! research test does.

use crate::l1::{prove_l1_wrap_in_memory, L1Proof, L1WrapTimings};
use crate::unified_transition::{
    prove_unified_transition_with_replayer_precommitted_timed,
    prove_unified_transition_with_replayer_timed, UnifiedTransitionTimings,
};
use full_statement_verifier::host_utils::{
    build_unified_stream, compute_end_params, load_fsv_program, load_program, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::{
    CommitmentMode, DefaultBabyBearBackend, DefaultBabyBearGKRBackend, WhirOracleStorage,
};
use prover::tests::gkr::orchestration::common::ProgramConfig;
use prover::worker::Worker;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

/// Cycle/RAM bounds of the BabyBear feeder stages (mirrors the research test).
const UNIFIED_CYCLES_BOUND: usize = 1 << 27;
const RAM_BOUND: usize = 1 << 30;
/// The final verifier run must fit the single 2^22 Proth120 unified chunk.
const L1_CYCLES_BOUND: usize = 1 << 22;

/// File stem of the MERGED-mode L1-feeder special-opcodes fsv binary (it has
/// no `FsvProgram` variant — the research test loads it by explicit path too).
const FEEDER_FSV_STEM: &str =
    "fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension";

/// Everything [`compress_fixed_point_to_l1`] produces: the L1 proof + its
/// commitment-mode aux data (the fixture pair the EVM tooling consumes) and
/// the per-stage timing breakdowns.
pub struct L1CompressionResult {
    pub l1_proof: L1Proof,
    pub l1_commitment_mode: CommitmentMode,
    /// BabyBear feeder stages 1 and 2.
    pub stage_timings: [UnifiedTransitionTimings; 2],
    /// The Proth120 packed stage 3.
    pub l1_timings: L1WrapTimings,
}

/// Compress the recursion stable point (1 unified + 1 blake proof) into the
/// single Proth120 packed L1 proof. See the module docs for the three stages.
///
/// * `input_proof` / `input_setups` — the converged pipeline artifact (must
///   carry a recursion chain; must be exactly 1 unified + 1 delegation proof).
/// * `fsv_dir` — the checked-in verifier programs, `tools/gkr_verifier`.
/// * `proth120_circuit_layout_path` — the compiled
///   `unified_reduced_machine_layout_gkr_proth120.json`.
/// * `feeder_storage` — the WHIR oracle storage policy of the BabyBear feeder
///   stages 1-2: `fully_in_memory()` on large machines (oracle recompute
///   otherwise dominates the chunk proving time), `fully_recompute()` where
///   the feeder-LDE codewords don't fit RAM. Stage 3 is always in-memory
///   ([`prove_l1_wrap_in_memory`]).
pub fn compress_fixed_point_to_l1(
    input_proof: &ProgramProof,
    input_setups: &Setups,
    fsv_dir: &Path,
    proth120_circuit_layout_path: &Path,
    use_caches: bool,
    feeder_storage: WhirOracleStorage,
    worker: &Worker,
) -> L1CompressionResult {
    let total_started = std::time::Instant::now();

    // The input must be the stable point: 1 unified chunk + 1 blake proof.
    let riscv_chunks: usize = input_proof.riscv_proofs.values().map(|v| v.len()).sum();
    let delegation_chunks: usize = input_proof
        .delegation_proofs
        .values()
        .map(|v| v.len())
        .sum();
    assert_eq!(
        riscv_chunks, 1,
        "input must be the converged stable point (1 unified chunk), got {riscv_chunks}"
    );
    assert_eq!(
        delegation_chunks, 1,
        "input must carry exactly 1 blake precompile proof, got {delegation_chunks}"
    );

    // Resume the recursion chain from the input's own preimage (= the chain
    // BEFORE the input's layer), then extend it with the input's end params so
    // the first stage chains onto the input.
    let preimage = input_proof
        .recursion_chain_preimage
        .expect("input proof must carry a recursion chain");
    let mut chain = FsvRecursionChain::resume(preimage);
    chain.extend(&compute_end_params(input_setups, input_proof.final_pc));

    // Stage-1 verifier: the STANDARD special-opcodes unified fsv (verifies
    // separate-commitment proofs). Stages 2/3: the MERGED-mode feeder fsv.
    let (std_bin, std_text) = load_fsv_program(
        fsv_dir,
        FsvProgram::UnifiedRecursionLayer,
        BlakeMode::BlakeSpecialOpcodes,
    );
    let (feeder_bin, feeder_text) = load_program(
        &fsv_dir.join(format!("{FEEDER_FSV_STEM}.bin")),
        &fsv_dir.join(format!("{FEEDER_FSV_STEM}.text")),
    );

    let feeder_config = prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23();
    println!(
        "[l1-compression] feeder config: base lde {}, whir steps {:?}, queries {:?}, pow {:?}; \
         feeder oracle storage: {feeder_storage:?}",
        feeder_config.lde_factor,
        feeder_config.whir_schedule.whir_steps_schedule,
        feeder_config.whir_schedule.whir_queries_schedule,
        feeder_config.whir_schedule.whir_pow_schedule,
    );

    // ── Stages 1 and 2: BabyBear feeder layers (merged commitments). ──
    let mut proof = input_proof.clone();
    let mut setups = input_setups.clone();
    let mut stage_timings = [UnifiedTransitionTimings::default(); 2];

    for stage in 0..2usize {
        let (run_bin, run_text) = if stage == 0 {
            (&std_bin, &std_text)
        } else {
            (&feeder_bin, &feeder_text)
        };
        println!(
            "[l1-compression] stage {}: proving the {} verifier over the current proof",
            stage + 1,
            if stage == 0 {
                "standard special-opcodes"
            } else {
                "merged-mode feeder"
            },
        );

        let stream = build_unified_stream(&setups, &proof);
        // Fully in-memory storage takes the precommitted single-pass path:
        // witness evaluation and the merged commitment happen once per chunk,
        // and the proofs consume the pre-committed oracles.
        let (mut new_proof, new_setups, timings) =
            if feeder_storage == WhirOracleStorage::fully_in_memory() {
                prove_unified_transition_with_replayer_precommitted_timed(
                    UNIFIED_CYCLES_BOUND,
                    run_bin,
                    run_text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(stream),
                    RAM_BOUND,
                    worker,
                    SecurityLevel::Sec100,
                    verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                    &feeder_config,
                    &DefaultBabyBearBackend::default(),
                    &DefaultBabyBearGKRBackend::default(),
                )
            } else {
                prove_unified_transition_with_replayer_timed(
                    UNIFIED_CYCLES_BOUND,
                    run_bin,
                    run_text,
                    use_caches,
                    QuasiUARTSource::new_with_reads(stream),
                    RAM_BOUND,
                    worker,
                    SecurityLevel::Sec100,
                    verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                    &feeder_config,
                    feeder_storage,
                    &DefaultBabyBearBackend::default(),
                    &DefaultBabyBearGKRBackend::default(),
                )
            };
        new_proof.set_recursion_chain(&chain);
        stage_timings[stage] = timings;

        let chunks: usize = new_proof.riscv_proofs.values().map(|v| v.len()).sum();
        let delegations: usize = new_proof.delegation_proofs.values().map(|v| v.len()).sum();
        assert_eq!(
            delegations, 0,
            "feeder layers are delegation-free by construction"
        );
        // The standard special-opcodes fsv run over the stable point costs
        // ~19.7M cycles = 3 feeder chunks; the feeder fsv over those 3 proofs
        // must contract to a single chunk for the L1 wrap.
        let expected_chunks = if stage == 0 { 3 } else { 1 };
        assert_eq!(
            chunks,
            expected_chunks,
            "stage {} must produce {expected_chunks} feeder chunk(s), got {chunks} — the \
             verifier cost / feeder schedule drifted",
            stage + 1,
        );
        println!(
            "[l1-compression] stage {}: {} cycles proven as {chunks} feeder chunk(s)",
            stage + 1,
            new_proof.executed_cycles(),
        );

        chain.extend(&compute_end_params(&new_setups, new_proof.final_pc));
        proof = new_proof;
        setups = new_setups;
    }

    // ── Stage 3: the same feeder verifier over the single feeder proof,
    //    proved with the Proth120 packed EVM-production parameters. ──
    println!(
        "[l1-compression] stage 3: proving the feeder verifier with the L1 (Proth120) parameters"
    );
    let stream = build_unified_stream(&setups, &proof);
    let program = ProgramConfig {
        binary_path: fsv_dir
            .join(format!("{FEEDER_FSV_STEM}.bin"))
            .to_string_lossy()
            .into_owned(),
        text_section_path: fsv_dir
            .join(format!("{FEEDER_FSV_STEM}.text"))
            .to_string_lossy()
            .into_owned(),
        non_determinism_reads: stream,
        cycles_bound: L1_CYCLES_BOUND,
        ram_bound_bytes: RAM_BOUND,
    };
    let (l1_proof, l1_commitment_mode, l1_timings) =
        prove_l1_wrap_in_memory(&program, proth120_circuit_layout_path, worker);

    // ── Timing marks: setup-commitment work vs proving work, per stage and
    //    in total. ──
    for (i, t) in stage_timings.iter().enumerate() {
        println!(
            "[timing] l1-compression stage {}: setup commit {}s, proofs {}s \
             (circuit setup {}s, merged tree commits {}s, witness eval {}s)",
            i + 1,
            t.setup_commit_ms / 1000,
            t.prove_ms / 1000,
            t.setup_ms / 1000,
            t.merged_tree_commit_ms / 1000,
            t.witness_eval_ms / 1000,
        );
    }
    println!(
        "[timing] l1-compression stage 3 (Proth120): setup commit {}s, proof {}s \
         (trace build {}s, setup {}s)",
        l1_timings.setup_commit_ms / 1000,
        l1_timings.prove_ms / 1000,
        l1_timings.trace_build_ms / 1000,
        l1_timings.setup_ms / 1000,
    );
    let total_setup_commit_ms: u128 = stage_timings
        .iter()
        .map(|t| t.setup_commit_ms)
        .sum::<u128>()
        + l1_timings.setup_commit_ms;
    let total_prove_ms: u128 =
        stage_timings.iter().map(|t| t.prove_ms).sum::<u128>() + l1_timings.prove_ms;
    println!(
        "[timing] l1-compression TOTAL: setup commitments {}s, proofs {}s, end-to-end {}s",
        total_setup_commit_ms / 1000,
        total_prove_ms / 1000,
        total_started.elapsed().as_millis() / 1000,
    );

    L1CompressionResult {
        l1_proof,
        l1_commitment_mode,
        stage_timings,
        l1_timings,
    }
}

#[cfg(test)]
mod diagnostics {
    use super::*;
    use crate::unified::replay_unified_circuit;
    use crate::unrolled::run_unrolled_machine_in_full;
    use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
    use riscv_transpiler::cycle::ReducedMachineWithDelegation;
    use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters};

    fn deserialize_compressed_from_file<T: serde::de::DeserializeOwned>(path: &str) -> T {
        use flate2::read::ZlibDecoder;
        use std::io::Read;
        let mut src = std::fs::File::open(path).unwrap_or_else(|e| panic!("open {path}: {e}"));
        let mut buffer = vec![];
        src.read_to_end(&mut buffer).unwrap();
        let mut decoder = ZlibDecoder::new(&buffer[..]);
        let mut unpacked: Vec<u8> = vec![];
        decoder.read_to_end(&mut unpacked).unwrap();
        bincode::deserialize_from(&unpacked[..]).unwrap()
    }

    /// Diagnostic: replay the stage-1 (standard special-opcodes fsv over the
    /// final_layer_0 stable point) tracer buffers and dump the rows around a
    /// failing chunk row together with the instruction words at their PCs.
    /// Row/chunk via `PROBE_ROW` / `PROBE_CHUNK` (defaults: the
    /// `EnforceSingleMaxQuadraticConstraintGKRKernel` divergence at row
    /// 7694852 of chunk 0). Run from the crate dir:
    /// `cargo test -p program_prover --features l1 --release probe_failing_cycle -- --ignored --nocapture`
    #[test]
    #[ignore = "diagnostic replay of the stage-1 trace around a failing row"]
    fn probe_failing_cycle() {
        let row: usize = std::env::var("PROBE_ROW")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(7_694_852);
        let chunk: usize = std::env::var("PROBE_CHUNK")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0);

        let tags = "blake2_with_compression_blake2_with_compression_blake2_with_compression";
        let proof: ProgramProof = deserialize_compressed_from_file(&format!(
            "../circuit_defs/prover_examples/final_layer_0_proof_{tags}.bin"
        ));
        let setups: Setups = deserialize_compressed_from_file(&format!(
            "../circuit_defs/prover_examples/final_layer_0_setups_{tags}.bin"
        ));
        let stream = build_unified_stream(&setups, &proof);
        let (bin, text) = load_fsv_program(
            "../tools/gkr_verifier",
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        );

        let (
            (final_pc, final_timestamp),
            snapshotter,
            counters,
            _ram,
            _registers,
            tape,
            expected_final_state,
        ) = run_unrolled_machine_in_full::<
            ReducedMachineWithDelegation,
            DelegationsAndUnifiedCounters,
        >(
            UNIFIED_CYCLES_BOUND,
            &bin,
            &text,
            RAM_BOUND,
            DelegationsAndUnifiedCounters::default(),
            riscv_transpiler::abstractions::non_determinism::QuasiUARTSource::new_with_reads(
                stream,
            ),
        );
        println!("execution ended at PC = 0x{final_pc:08x}, timestamp {final_timestamp}");

        let num_calls =
            counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
        let buffers = replay_unified_circuit::<DelegationsAndUnifiedCounters>(
            DelegationsAndUnifiedCounters::default(),
            &snapshotter,
            &tape,
            UNIFIED_CYCLES_BOUND,
            1 << 23,
            &expected_final_state,
            num_calls,
        );
        let buf = &buffers[chunk];
        println!("chunk {chunk}: {} tracer rows", buf.len());

        let lo = row.saturating_sub(4);
        let hi = (row + 4).min(buf.len().saturating_sub(1));
        for r in lo..=hi {
            let el = &buf[r];
            let pc = el.initial_pc();
            let word = text.get((pc / 4) as usize).copied().unwrap_or(u32::MAX);
            let marker = if r == row { "  <<< FAILING ROW" } else { "" };
            println!(
                "row {r}: pc=0x{pc:08x} word=0x{word:08x} (opcode=0x{:02x} rd={} funct3={} rs1={} rs2={} funct7=0x{:02x}){marker}",
                word & 0x7f,
                (word >> 7) & 0x1f,
                (word >> 12) & 0x7,
                (word >> 15) & 0x1f,
                (word >> 20) & 0x1f,
                (word >> 25) & 0x7f,
            );
            println!("        {el:?}");
        }
    }
}
