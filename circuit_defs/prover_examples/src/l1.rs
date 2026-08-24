//! The L1 wrap: prove a (delegation-free) RISC-V run as ONE Proth120 packed
//! unified-circuit proof with the exact EVM-production parameters — the proof
//! shape the deployed gkr.sol/whir.sol two-transaction verifier consumes.
//!
//! Mirrors the reference flow of
//! `prover::tests::gkr::large_field::gkr_unified_packed_commitment_basic_fibonacci`
//! in its memory-light configuration, which is the only mode this driver
//! offers: memory/witness RS codewords, intermediate WHIR oracles AND the
//! packed setup commitment all served by coset RECOMPUTATION — the ~2^31
//! packed codewords never materialize in RAM and nothing is cached on disk. External challenges are SELF-DERIVED by the packed
//! commitment mode from the run's boundary state (registers, final PC/ts)
//! behind a PoW grind, so no pre-challenge memory commits exist.
//!
//! Intended use: the last BabyBear recursion artifact (the merged-mode L1
//! feeder proof) is verified by the feeder full-statement verifier in
//! ~2.8M cycles <= 2^22 — proving THAT run here yields the single proof L1
//! verifies on-chain.

use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::definitions::FinalRegisterValue;
use prover::fft::Twiddles;
use prover::field::Proth120;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::prover::{
    prove_configured_with_gkr_with_storage_and_backend, CommitmentMode, GKRProof, NaiveGKRBackend,
    Proth120WorkStealingLazyBackend, SetupCommitment, WhirOracleStorage,
};
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::gkr::whir::ColumnMajorBaseOracleForLDE;
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

fn serialize_pretty_to_file<T: serde::Serialize>(el: &T, path: &Path) {
    let mut dst =
        std::fs::File::create(path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

/// Prove `program`'s execution as a single Proth120 packed unified proof in
/// the recompute (memory-light) mode with the EVM-production parameters, and
/// write the proof + its `CommitmentMode` aux data (the boundary state the
/// EVM transcript recipe replays) as pretty JSON — the exact fixture pair the
/// verifier_evm generation and the two-transaction test consume.
///
/// `circuit_layout_path` is the compiled
/// `unified_reduced_machine_layout_gkr_proth120.json`. The run must fit one
/// 2^22 chunk and make no delegation calls.
#[allow(clippy::too_many_arguments)]
pub fn prove_l1_wrap_in_recompute_mode(
    program: &ProgramConfig,
    circuit_layout_path: &Path,
    proof_output_path: &Path,
    aux_output_path: &Path,
    worker: &Worker,
) -> L1Proof {
    let pack_log2 = EVM_PRODUCTION_PACK_LOG2;
    let external_challenges_pow_bits = EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS;
    let level = prover::definitions::SecurityLevel::Sec100;
    let prover_config = evm_production_packed_prover_config(level);
    let trace_len = 1usize << prover_config.trace_len_log2;

    // 1. Run the program on the reduced machine and capture the execution.
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

    // 4. Packed twiddles: the commitment interpolates the packed polynomials
    //    over the 2^(22 + pack_log2) domain.
    let packed_twiddles: Twiddles<Proth120, std::alloc::Global> =
        Twiddles::new(trace_len << pack_log2, worker);

    // 5. Setup commitment by COSET RECOMPUTATION: the packed setup codeword
    //    (~2^31 elements) is never materialized or cached — the commitment cap
    //    is computed coset-by-coset from the packed monomial forms and round-0
    //    setup queries recompute their cosets on demand. The setup CONTENT
    //    depends on the PROGRAM (its decoder table is built from the binary),
    //    so recomputation also removes the stale-cache hazard an on-disk setup
    //    shared between programs would have.
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &unified_circuit);

    let lde_factor = prover_config.lde_factor;
    let values_per_leaf = prover_config.base_oracles_values_per_leaf;

    println!("L1 wrap: committing setup by coset recomputation (packed)");
    let setup_inputs: Vec<&[Proth120]> = setup.hypercube_evals.iter().map(|el| &el[..]).collect();
    let setup_commitment = SetupCommitment::InMemory(ColumnMajorBaseOracleForLDE::CosetRecompute(
        CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit_packed(
            &setup_inputs,
            &packed_twiddles,
            lde_factor,
            values_per_leaf.trailing_zeros() as usize,
            prover_config.cap_size,
            prover_config.trace_len_log2,
            pack_log2,
            worker,
        ),
    ));

    // 6. Prove the single unified instance with the packed commitment mode
    //    (self-derived external challenges from the boundary state).
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

    println!("L1 wrap: proving (packed, recompute, pack_log2 = {pack_log2})");
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
        WhirOracleStorage::fully_recompute(),
        top_bits,
        trace_len,
        &Proth120WorkStealingLazyBackend,
        &NaiveGKRBackend,
        worker,
    );
    println!(
        "L1 wrap: packed unified proving time is {:?}",
        now.elapsed()
    );

    serialize_pretty_to_file(&proof, proof_output_path);
    serialize_pretty_to_file(&commitment_mode, aux_output_path);
    println!(
        "L1 wrap: wrote {} and {}",
        proof_output_path.display(),
        aux_output_path.display()
    );

    proof
}
