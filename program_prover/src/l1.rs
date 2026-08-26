//! The L1 wrap, ALL-IN-MEMORY flavor: prove a (delegation-free) RISC-V run as
//! ONE Proth120 packed unified-circuit proof with the exact EVM-production
//! parameters — the proof shape the deployed gkr.sol/whir.sol two-transaction
//! verifier consumes.
//!
//! Analog of `prover_examples::l1::prove_l1_wrap_in_recompute_mode`, with the
//! opposite storage policy: the packed setup is committed fully in memory
//! (`GKRSetup::commit_packed`, no coset recomputation and no on-disk staging)
//! and the memory/witness base + intermediate WHIR oracles are fully
//! materialized, intermediates in one contiguous buffer per oracle
//! (`WhirOracleStorage::fully_in_memory_continuous()`). Meant for large
//! machines that can hold the ~2^31 packed RS codewords (several hundred GiB
//! working set); the produced proof is byte-identical to the recompute-based
//! run. Mirrors the storage choices of the prover test
//! `gkr_unified_packed_commitment_basic_fibonacci_64core_in_memory`.
//!
//! External challenges are SELF-DERIVED by the packed commitment mode from the
//! run's boundary state (registers, final PC/ts) behind a PoW grind, so no
//! pre-challenge memory commits exist.

use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::definitions::FinalRegisterValue;
use prover::fft::Twiddles;
use prover::field::Proth120;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::prover::{
    prove_configured_with_gkr_with_storage_and_backend, CommitmentMode, GKRProof, NaiveGKRBackend,
    Proth120WorkStealingLazyBackend, SetupCommitment, WhirOracleStorage,
};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::tests::gkr::large_field::{
    build_unified_trace_without_precompiles, evm_production_packed_prover_config,
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};
use prover::tests::gkr::orchestration::common::{
    dummy_external_challenges, run_vm_and_capture, ProgramConfig,
};
use prover::tests::gkr::unified_reduced_machine_proth120;
use prover::transcript::Keccak256Transcript;
use prover::worker::Worker;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use std::path::Path;

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

/// Wall-clock breakdown of one [`prove_l1_wrap_in_memory`] run.
#[derive(Clone, Copy, Debug, Default)]
pub struct L1WrapTimings {
    /// VM run + unified witness trace build.
    pub trace_build_ms: u128,
    /// `GKRSetup::construct` (tables + setup hypercube evals).
    pub setup_ms: u128,
    /// The in-memory packed setup commitment (`GKRSetup::commit_packed`).
    pub setup_commit_ms: u128,
    /// The packed `prove_configured_*` call (includes the in-proof merged
    /// memory+witness commitment — the packed mode commits it itself).
    pub prove_ms: u128,
}

/// Prove `program`'s execution as a single Proth120 packed unified proof with
/// ALL oracles in memory and the EVM-production parameters. Returns the proof,
/// the `CommitmentMode` aux data (the boundary state the EVM transcript recipe
/// replays — the exact fixture pair the verifier_evm generation and the
/// two-transaction test consume), and the timing breakdown.
///
/// `circuit_layout_path` is the compiled
/// `unified_reduced_machine_layout_gkr_proth120.json`. The run must fit one
/// 2^22 chunk and make no delegation calls.
pub fn prove_l1_wrap_in_memory(
    program: &ProgramConfig,
    circuit_layout_path: &Path,
    worker: &Worker,
) -> (L1Proof, CommitmentMode, L1WrapTimings) {
    let mut timings = L1WrapTimings::default();
    let pack_log2 = EVM_PRODUCTION_PACK_LOG2;
    let external_challenges_pow_bits = EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS;
    let level = prover::definitions::SecurityLevel::Sec100;
    let prover_config = evm_production_packed_prover_config(level);
    let trace_len = 1usize << prover_config.trace_len_log2;

    // 1. Run the program on the reduced machine and capture the execution.
    let trace_started = std::time::Instant::now();
    let vm = run_vm_and_capture::<DelegationsAndUnifiedCounters, ReducedMachineDecoderConfig>(
        program, worker,
    );
    println!(
        "L1 wrap: program finished at PC = 0x{:08x}, timestamp {}",
        vm.final_pc(),
        vm.final_timestamp()
    );

    // 2. Load the Proth120 unified circuit.
    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(circuit_layout_path)
            .unwrap_or_else(|e| panic!("open {}: {e}", circuit_layout_path.display()));
        serde_json::from_reader(src).expect("deserialize unified circuit")
    };
    let num_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();

    // 3. Build the unified witness trace (asserts the run is delegation-free
    //    and fits a single 2^22 chunk).
    let (full_trace, table_driver, decoder_table, top_bits) =
        build_unified_trace_without_precompiles(
            &vm,
            unified_reduced_machine_proth120::witness_eval_fn,
            &unified_circuit,
            num_teardown_sets,
            trace_len,
            worker,
        );
    timings.trace_build_ms = trace_started.elapsed().as_millis();

    // 4. Packed twiddles: the commitment interpolates the packed polynomials
    //    over the 2^(22 + pack_log2) domain.
    let packed_twiddles: Twiddles<Proth120, std::alloc::Global> =
        Twiddles::new(trace_len << pack_log2, worker);

    // 5. Setup, then its FULLY IN-MEMORY packed commitment: RS codewords and
    //    the monolithic Merkle tree are materialized (byte-identical
    //    commitment to the coset-recompute/on-disk paths).
    let setup_started = std::time::Instant::now();
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &unified_circuit);
    timings.setup_ms = setup_started.elapsed().as_millis();

    let lde_factor = prover_config.lde_factor;
    let values_per_leaf = prover_config.base_oracles_values_per_leaf;

    println!("L1 wrap: committing setup in memory (packed)");
    let setup_commit_started = std::time::Instant::now();
    let setup_commitment =
        SetupCommitment::InMemory(setup.commit_packed::<Keccak256MerkleTreeWithCap>(
            &packed_twiddles,
            lde_factor,
            values_per_leaf.trailing_zeros() as usize,
            prover_config.cap_size,
            prover_config.trace_len_log2,
            pack_log2,
            worker,
        ));
    timings.setup_commit_ms = setup_commit_started.elapsed().as_millis();

    // 6. Prove the single unified instance with the packed commitment mode
    //    (self-derived external challenges from the boundary state) and every
    //    oracle materialized in RAM.
    let external_challenges = dummy_external_challenges::<Proth120, Proth120>();

    let commitment_mode = CommitmentMode::MergedAndPackedMemoryAndWitness {
        pack_log2,
        external_challenges_pow_bits,
        final_pc: vm.final_pc(),
        final_timestamp: vm.final_timestamp(),
        register_final_state: vm.register_final_state().map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        }),
    };

    println!("L1 wrap: proving (packed, in-memory oracles, pack_log2 = {pack_log2})");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr_with_storage_and_backend::<
        Proth120,
        Proth120,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
        _,
        _,
    >(
        &unified_circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &packed_twiddles,
        &prover_config,
        commitment_mode.clone(),
        WhirOracleStorage::fully_in_memory_continuous(),
        top_bits,
        trace_len,
        &Proth120WorkStealingLazyBackend,
        &NaiveGKRBackend,
        worker,
    );
    timings.prove_ms = now.elapsed().as_millis();
    println!(
        "L1 wrap: packed unified proving time is {:?}",
        now.elapsed()
    );

    (proof, commitment_mode, timings)
}
