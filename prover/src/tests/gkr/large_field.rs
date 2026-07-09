//! Packed-commitment exploration test.
//!
//! Runs the plain `basic_fibonacci` program (reduced machine, no oracles, no
//! precompiles) and TRIES to prove one unified-circuit instance with the packed
//! commitment mode
//! [`CommitmentMode::MergedAndPackedMemoryAndWitness`](crate::gkr::prover::CommitmentMode).
//!
//! Notes vs the full `unified_circuit.rs` flow:
//!   * precompiles are DISABLED at preprocessing — the supported-CSR set passed to
//!     `process_binary_into_separate_tables_ext` contains only the non-determinism
//!     CSR (no delegation CSRs), so no delegation family is produced;
//!   * external challenges are the hardcoded ones (no Fiat-Shamir memory transcript);
//!   * the twiddles handed to the proof function are of the UNIFIED CIRCUIT SIZE
//!     `<< pack_log2` (the packed commitment interpolates over the enlarged domain),
//!     while the setup commitment uses ordinary trace-sized twiddles.

use super::orchestration::common::{
    run_vm_and_capture, ProgramConfig, VmRunOutput, NUM_CYCLES_PER_CHUNK,
};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::CommitmentMode;
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_witness_for_executor_family, GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::tests::gkr::orchestration::common::dummy_external_challenges;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
    UnifiedReducedMachineDecoder,
};
use cs::tables::TableDriver;
use fft::Twiddles;
use field::{PrimeField, Proth120};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use transcript::{Blake2sTranscript, Keccak256Transcript};
use worker::Worker;

/// `basic_fibonacci`: computes the 10th fibonacci number, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
fn basic_fibonacci_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/basic_fibonacci/app.bin".to_string(),
        text_section_path: "../examples/basic_fibonacci/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

const TRACE_LEN_LOG2: usize = 24;

#[test]
fn gkr_unified_packed_commitment_basic_fibonacci_sec_80() {
    let worker = Worker::new_with_num_threads(8);
    let level = SecurityLevel::Sec80;
    let pack_log2 = 2usize;
    let external_challenges_pow_bits = 0u32;

    // 1. Run the plain fibonacci program (reduced machine, no precompiles).
    let config = basic_fibonacci_config();
    let vm = run_vm_and_capture::<DelegationsAndUnifiedCounters, ReducedMachineDecoderConfig>(
        &config, &worker,
    );
    println!("Finished at PC = 0x{:08x}", vm.final_pc());

    // 2. Load the unified reduced-machine circuit.
    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .expect("unified circuit layout");
        serde_json::from_reader(src).expect("deserialize unified circuit")
    };
    let num_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    // 3. Build the unified witness trace with precompiles disabled at preprocessing.
    let (full_trace, table_driver, decoder_table) = build_unified_trace_without_precompiles(
        &vm,
        super::unified_reduced_machine_proth120::witness_eval_fn,
        &unified_circuit,
        num_teardown_sets,
        &worker,
    );

    println!("Preparing data for proving");
    // 4. Prover config for 80 bits + twiddles.
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        TRACE_LEN_LOG2,
        level,
    );

    println!("Computing setup");
    // The proof function's twiddles are of unified circuit size * (1 << pack_log2):
    // the packed commitment interpolates the merged/packed polynomials over the
    // enlarged domain.
    let packed_twiddles: Twiddles<Proth120, Global> =
        Twiddles::new(trace_len << pack_log2, &worker);

    // 5. Construct & commit the setup.
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &unified_circuit);
    println!("Computing setup commitment");
    let setup_commitment = setup.commit_packed::<Keccak256MerkleTreeWithCap>(
        &packed_twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        TRACE_LEN_LOG2,
        pack_log2,
        &worker,
    );

    // 6. Prove one unified circuit instance with the packed commitment mode.
    let external_challenges = dummy_external_challenges::<Proth120, Proth120>();
    let top_bits: Vec<u32> = (0..num_teardown_sets).map(|i| i as u32).collect();

    println!("Trying to prove (unified, packed commitment, pack_log2 = {pack_log2})");
    let now = std::time::Instant::now();
    let _proof = prove_configured_with_gkr::<
        Proth120,
        Proth120,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
    >(
        &unified_circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &packed_twiddles,
        &prover_config,
        CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2,
            external_challenges_pow_bits,
        },
        top_bits,
        trace_len,
        &worker,
    );
    println!("Packed unified proving time is {:?}", now.elapsed());
}

/// Inlined analogue of `orchestration::unified::build_unified_full_trace`, but with
/// the delegation CSRs removed from the preprocessing supported-CSR set (precompiles
/// disabled at preprocessing) and without the optional memory-consistency cross-check.
fn build_unified_trace_without_precompiles<C, F: PrimeField>(
    vm: &VmRunOutput<C>,
    witness_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, F>),
    unified_circuit: &GKRCircuitArtifact<F>,
    num_teardown_sets: usize,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<F, Global, Global>,
    TableDriver<F>,
    Vec<Option<ExecutorFamilyDecoderData>>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    println!("Replaying {} cycles for witness data", num_calls);
    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    // Preprocessing WITHOUT any delegation CSRs => no precompiles.
    println!("Creating decoder table");
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[common_constants::NON_DETERMINISM_CSR as u16];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer,
        decoder_table: &decoder_table,
    };
    let unified_table_driver = build_unified_table_driver::<F>(&vm.binary);

    // Inits/teardown columns sized to the unified circuit's set count.
    let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
    for _ in 0..num_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        inits_and_teardowns.push(([a, b], [c, d]));
    }
    println!("Collecting inits and teardowns");
    vm.ram.collect_inits_and_teardowns_into_columns::<F, _>(
        worker,
        TRACE_LEN_LOG2,
        0,
        &mut inits_and_teardowns,
    );

    println!("Calculating full witness trace");
    let full_trace = evaluate_gkr_witness_for_executor_family::<F, _, _, _>(
        unified_circuit,
        witness_eval_fn_ptr,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &unified_table_driver,
        worker,
        Some(inits_and_teardowns),
        Global,
        Global,
    );

    (full_trace, unified_table_driver, decoder_table)
}
