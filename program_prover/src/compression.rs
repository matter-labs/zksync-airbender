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
//!    verifies the input pair; proving that run takes one or more 2^23 feeder
//!    chunks.
//! 2. The MERGED-mode feeder fsv (the pinned `FsvProfile::L1Feeder` guest of
//!    the unified recursion layer, special opcodes) verifies those feeder
//!    proofs; proving it must fit ONE feeder chunk.
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
    build_unified_stream, compute_end_params, fsv_manifest_entry, load_fsv_exact, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::{SecurityLevel, SoundnessMode};
use prover::gkr::prover::{
    DefaultBabyBearBackend, DefaultBabyBearGKRBackend, OperationMode, RsCodewordSource,
    WhirOracleStorage,
};
use prover::worker::Worker;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

/// Cycle/RAM bounds of the BabyBear feeder stages (mirrors the research test).
const UNIFIED_CYCLES_BOUND: usize = 1 << 27;
const RAM_BOUND: usize = 1 << 30;
/// The final verifier run must fit the single 2^22 Proth120 unified chunk.
const L1_CYCLES_BOUND: usize = 1 << 22;

/// The MERGED-mode L1-feeder guest: the unified recursion layer with special
/// opcodes, under the pinned `L1Feeder` profile.
const L1_FEEDER_GUEST: FsvDescriptor = FsvDescriptor {
    profile: FsvProfile::L1Feeder,
    ..FsvDescriptor::new(
        SecurityLevel::Sec100,
        SoundnessMode::PessimisticConjecture,
        FsvProgram::UnifiedRecursionLayer,
        BlakeMode::BlakeSpecialOpcodes,
    )
};

/// The L1-feeder guest, read once through its pin ([`load_fsv_exact`]): the
/// ROM-padded words the BabyBear stages prove and the unpadded image and text
/// the Proth120 stage runs. Both are views of the same verified file.
struct FeederGuest {
    bin: Vec<u32>,
    text: Vec<u32>,
    unpadded_bin: Vec<u32>,
    unpadded_text: Vec<u32>,
}

/// Load [`L1_FEEDER_GUEST`] from `fsv_dir`; panics as [`load_fsv_exact`] does on
/// any file other than the pinned one.
fn load_feeder_guest(fsv_dir: &Path) -> FeederGuest {
    let (bin, text) = load_fsv_exact(fsv_dir, &L1_FEEDER_GUEST).into_words();
    // The pinned sizes of the same image: the ROM padding and the text
    // padding are trailing zero words.
    let pinned = fsv_manifest_entry(&L1_FEEDER_GUEST);
    let unpadded_bin = bin[..pinned.rom_bytes / 4].to_vec();
    let unpadded_text = text[..pinned.text_bytes / 4].to_vec();
    FeederGuest {
        bin,
        text,
        unpadded_bin,
        unpadded_text,
    }
}

/// Everything [`compress_fixed_point_to_l1`] produces: the L1 proof + its
/// commitment-mode aux data (the fixture pair the EVM tooling consumes) and
/// the per-stage timing breakdowns.
pub struct L1CompressionResult {
    pub l1_proof: L1Proof,
    pub l1_operation_mode: OperationMode,
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
/// * `fsv_dir` — the checked-in verifier programs, `tools/gkr_verifier/full_statement_verifiers`.
/// * `proth120_circuit_layout_path` — the compiled
///   `unified_reduced_machine_layout_gkr_proth120.json`.
/// * `feeder_storage` — the WHIR oracle storage policy of the BabyBear feeder
///   stages 1-2: `fully_in_memory_continuous()` on large machines (oracle
///   recompute otherwise dominates the chunk proving time),
///   `fully_recompute()` where the feeder-LDE codewords don't fit RAM. Stage
///   3 is always in-memory-continuous ([`crate::l1::prove_l1_wrap_in_memory`]).
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
    let (std_bin, std_text) = load_fsv_exact(
        fsv_dir,
        &FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        ),
    )
    .into_words();
    let feeder = load_feeder_guest(fsv_dir);

    let feeder_config = prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23();
    println!(
        "[l1-compression] feeder config: base lde {}, whir steps {:?}, queries {:?}, pow {:?}; \
         feeder oracle storage: {feeder_storage:?}",
        feeder_config.lde_factor(),
        feeder_config.whir_schedule.fold_steps(),
        feeder_config.whir_schedule.queries_per_round(),
        feeder_config.whir_schedule.queries_pow_bits_per_round(),
    );

    // ── Stages 1 and 2: BabyBear feeder layers (merged commitments). ──
    let mut proof = input_proof.clone();
    let mut setups = input_setups.clone();
    let mut stage_timings = [UnifiedTransitionTimings::default(); 2];

    for (stage, stage_timing) in stage_timings.iter_mut().enumerate() {
        let (run_bin, run_text) = if stage == 0 {
            (&std_bin, &std_text)
        } else {
            (&feeder.bin, &feeder.text)
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

        let stream = build_unified_stream(&setups, &proof, BlakeMode::BlakeSpecialOpcodes);
        // An in-memory base source takes the precommitted single-pass path:
        // witness evaluation and the merged commitment happen once per chunk,
        // and the proofs consume the pre-committed oracles (the
        // intermediate-oracle mode of `feeder_storage` is passed through).
        let (mut new_proof, new_setups, timings) =
            if feeder_storage.base_rs_source == RsCodewordSource::InMemory {
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
                    feeder_storage,
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
        *stage_timing = timings;

        let chunks: usize = new_proof.riscv_proofs.values().map(|v| v.len()).sum();
        let delegations: usize = new_proof.delegation_proofs.values().map(|v| v.len()).sum();
        assert_eq!(
            delegations, 0,
            "feeder layers are delegation-free by construction"
        );
        // The standard special-opcodes fsv run over the stable point may take
        // several feeder chunks; the feeder fsv over them must contract to a
        // single chunk for the L1 wrap.
        assert!(chunks > 0, "stage {} produced no feeder chunk", stage + 1);
        if stage == 1 {
            assert_eq!(
                chunks, 1,
                "stage 2 must contract to one feeder chunk for the L1 wrap, got {chunks} — the \
                 verifier cost / feeder schedule drifted"
            );
        }
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
    let stream = build_unified_stream(&setups, &proof, BlakeMode::BlakeSpecialOpcodes);
    let (l1_proof, l1_operation_mode, l1_timings) = prove_l1_wrap_in_memory(
        feeder.unpadded_bin,
        feeder.unpadded_text,
        &stream,
        L1_CYCLES_BOUND,
        RAM_BOUND,
        proth120_circuit_layout_path,
        worker,
    );

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
        l1_operation_mode,
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
        full_statement_verifier::host_utils::fixture_codec::decode(
            &std::fs::read(path).unwrap_or_else(|error| panic!("read {path}: {error}")),
        )
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
            "../circuit_defs/prover_examples/final_layer_0_proof_{tags}.json.zlib"
        ));
        let setups: Setups = deserialize_compressed_from_file(&format!(
            "../circuit_defs/prover_examples/final_layer_0_setups_{tags}.json.zlib"
        ));
        let stream = build_unified_stream(&setups, &proof, BlakeMode::BlakeSpecialOpcodes);
        let (bin, text) = load_fsv_exact(
            "../tools/gkr_verifier/full_statement_verifiers",
            &FsvDescriptor::new(
                SecurityLevel::Sec100,
                SoundnessMode::PessimisticConjecture,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
            ),
        )
        .into_words();

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
        for (r, el) in buf.iter().enumerate().take(hi + 1).skip(lo) {
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

#[cfg(test)]
mod feeder_guest_tests {
    use super::*;
    use full_statement_verifier::host_utils::{canonical_fsv_dir, load_program};
    use riscv_transpiler::elf::ProgramSource;

    fn feeder_path(fsv_dir: &Path) -> std::path::PathBuf {
        fsv_dir.join(L1_FEEDER_GUEST.registry_entry().unwrap().relative_path)
    }

    /// The pinned feeder words are what each stage read from the file before the pin: the
    /// ROM-padded words of `load_program` (stages 1 and 2) and the unpadded words of
    /// `ProgramSource::load_unpadded` (stage 3).
    #[test]
    fn pinned_feeder_words_match_the_unpinned_reads() {
        let feeder = load_feeder_guest(&canonical_fsv_dir());
        let path = feeder_path(&canonical_fsv_dir());
        assert_eq!((feeder.bin, feeder.text), load_program(&path));
        assert_eq!(
            (feeder.unpadded_bin, feeder.unpadded_text),
            ProgramSource::elf(&path).load_unpadded()
        );
    }

    struct ScratchDir(std::path::PathBuf);

    impl Drop for ScratchDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// The standard special-opcodes guest placed at the feeder path is refused.
    #[test]
    #[should_panic(
        expected = "holds the full-statement verifier sec_100/pessimistic_conjecture/unified_recursion_layer/standard/"
    )]
    fn another_guest_at_the_feeder_path_is_refused() {
        let dir = ScratchDir(
            std::env::temp_dir().join(format!("l1-feeder-guest-{}", std::process::id())),
        );
        let standard = FsvDescriptor {
            profile: FsvProfile::Standard,
            ..L1_FEEDER_GUEST
        };
        let to = feeder_path(&dir.0);
        std::fs::create_dir_all(to.parent().unwrap()).unwrap();
        std::fs::copy(
            canonical_fsv_dir().join(standard.registry_entry().unwrap().relative_path),
            &to,
        )
        .unwrap();
        load_feeder_guest(&dir.0);
    }
}
