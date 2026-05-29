use super::*;
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::prover::GKRProof;
use crate::gkr::prover::WhirSchedule;
use crate::gkr::prover_config;
use crate::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use cs::definitions::*;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use fft::materialize_powers_serial_starting_with_elem;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::simple_instruction_set::Instruction;
use riscv_transpiler::replayer::*;
use riscv_transpiler::witness::*;
use std::alloc::Global;
use worker::Worker;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const RAM_BOUND_BYTES: usize = 1 << 30;

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

// jump_branch_slt multiplicity column indices (from compiled circuit witness_layout)
const MULTIPLICITY_COL_RANGE_CHECK_16: usize = 25;
const MULTIPLICITY_COL_TIMESTAMP: usize = 26;
const MULTIPLICITY_COL_GENERIC: usize = 27;

/// Generate a jump_branch_slt proof with a witness mutation applied before proving.
fn generate_proof(
    mutate: impl FnOnce(&mut GKRFullWitnessTrace<BabyBearField, Global, Global>),
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;

    type CountersT = DelegationsAndFamiliesCounters;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let prover_config =
        prover_config::example_configs::config_for_80_bits_under_pessimistic_conjecture(
            TRACE_LEN_LOG2,
        );
    let worker = Worker::new_with_num_threads(8);

    let binary = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.bin").unwrap();
    let text_section = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.text").unwrap();

    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        &binary,
        RAM_BOUND_BYTES,
    );
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { common_constants::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound, state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let _is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let memory_argument_alpha = BabyBearExt4::from_array_of_base([
        BabyBearField::new(2),
        BabyBearField::new(5),
        BabyBearField::new(42),
        BabyBearField::new(123),
    ]);
    let permutation_argument_additive_part = BabyBearExt4::from_array_of_base([
        BabyBearField::new(7),
        BabyBearField::new(11),
        BabyBearField::new(1024),
        BabyBearField::new(8000),
    ]);

    let permutation_argument_linearization_challenges: [BabyBearExt4;
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );

    const CIRCUIT_TYPE: u8 = JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

    let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
        deserialize_from_file(
            "../cs/compiled_circuits/jump_branch_slt_preprocessed_layout_gkr.json",
        )
    } else {
        deserialize_from_file(
            "../cs/compiled_circuits/jump_branch_slt_preprocessed_layout_no_caches_gkr.json",
        )
    };

    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn(&mut table_driver);

    let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(
        num_calls > 0,
        "no jump_branch_slt instructions found in trace"
    );

    let mut state = snapshotter.initial_snapshot.state;

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<CIRCUIT_TYPE> {
        buffers: &mut buffers[..],
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|el| el.unwrap_or(Default::default()))
        .collect::<Vec<_>>();

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
        default_pc_value_in_padding: 4,
    };

    assert!(
        !oracle.inner.is_empty(),
        "oracle must not be empty for malicious proof"
    );

    println!("Computing full trace");
    let mut full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        &circuit,
        jump_branch_slt::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        Global,
        Global,
    );

    println!("Applying witness mutation");
    mutate(&mut full_trace);

    println!("Preparing twiddles");
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    println!("Preparing setup");
    let setup = GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    println!("Proving with corrupted witness");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor, _>(
        &circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        Vec::new(),
        trace_len,
        Option::<()>::None,
        &worker,
    );
    println!("Malicious proving time: {:?}", now.elapsed());

    proof
}

#[test]
#[ignore]
fn generate_malicious_proofs() {
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_RANGE_CHECK_16;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "range_check_16 multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(&proof, "test_proofs/malicious_lookup_16bits_gkr_proof.json");

    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_TIMESTAMP;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "timestamp multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_timestamps_gkr_proof.json",
    );

    // Generic lookup via multiplicity corruption
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_GENERIC;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "generic multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_generic_gkr_proof.json",
    );

    // --- Constraint / permutation violations ---

    let proof = generate_proof(|trace| {
        trace.column_major_witness_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_witness_value_gkr_proof.json");

    let proof = generate_proof(|trace| {
        trace.column_major_memory_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_memory_value_gkr_proof.json");
}
