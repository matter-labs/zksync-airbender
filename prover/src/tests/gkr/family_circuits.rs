use super::*;
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::prover::WhirSchedule;
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_memory_witness_for_delegation_circuit;
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use crate::gkr::witness_gen::family_circuits::evaluate_gkr_memory_witness_for_executor_family;
use crate::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use crate::gkr::witness_gen::oracles::MemoryCircuitOracle;
use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::tracers::oracles::transpiler_oracles::delegation::*;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use common_constants::TIMESTAMP_STEP;
use cs::definitions::INITIAL_TIMESTAMP;
use cs::definitions::*;
use cs::gkr_circuits::mem_word_only_table_driver_fn;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use fft::materialize_powers_serial_starting_with_elem;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::simple_instruction_set::Instruction;
use riscv_transpiler::ir::*;
use riscv_transpiler::replayer::*;
use riscv_transpiler::witness::*;
use std::alloc::Global;
use std::collections::BTreeSet;
use worker::Worker;

const INITIAL_PC: u32 = 0;
const NUM_INIT_AND_TEARDOWN_SETS: usize = 8;

// NOTE: these constants must match with ones used in CS crate to produce
// layout and SSA forms, otherwise derived witness-gen functions may write into
// invalid locations
const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const BLAKE_NUM_DELEGATION_CYCLES: usize = 1 << 20;
const BIGINT_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const KECCAK_NUM_DELEGATION_CYCLES: usize = 1 << 22;

const PROVE_ADD_SUB: bool = true;
const PROVE_JUMP_BRANCH: bool = true;
const PROVE_SHIFTS_BINOPS: bool = true;
const PROVE_MEM_WORD: bool = true;
const PROVE_MEM_SUBWORD: bool = true;
const PROVE_BLAKE: bool = true;
const PROVE_BIGINT: bool = true;
const PROVE_KECCAK: bool = true;

// #[ignore = "test has explicit panic inside"]
#[test]
fn gkr_run_basic_unrolled_test() {
    gkr_run_basic_unrolled_test_impl(None, None);
}

pub fn gkr_run_basic_unrolled_test_impl(
    maybe_gpu_unrolled_comparison_hook: Option<Box<dyn Fn()>>,
    maybe_gpu_delegation_comparison_hook: Option<Box<dyn Fn()>>,
) {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;

    type CountersT = DelegationsAndFamiliesCounters;

    const CHECK_MEMORY_PERMUTATION_ONLY: bool = false;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    // let worker = Worker::new_with_num_threads(1);
    let worker = Worker::new_with_num_threads(8);
    // load binary

    // let binary = std::fs::read("../examples/basic_fibonacci/app.bin").unwrap();
    // let text_section = std::fs::read("../examples/basic_fibonacci/app.text").unwrap();

    // let binary = std::fs::read("../examples/hashed_fibonacci/app.bin").unwrap();
    // let text_section = std::fs::read("../examples/hashed_fibonacci/app.text").unwrap();

    let binary = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.bin").unwrap();
    let text_section = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.text").unwrap();

    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    assert!(text_section.len() % 4 == 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // first run to capture minimal information
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        &binary,
        1 << 30,
    );
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::<CountersT, {common_constants::ROM_SECOND_WORD_BITS}>::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished); // check that we reached looping state (ie. end state for our vm)

    dbg!(state.counters);

    let total_snapshots = snapshotter.snapshots.len();

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    // let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
    //     1,
    //     NUM_CYCLES_PER_CHUNK * NUM_INIT_AND_TEARDOWN_SETS,
    //     &shuffle_ram_touched_addresses,
    //     &worker,
    // );
    // assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
        .into_iter()
        .flatten()
        .collect();

    println!("Finished at PC = 0x{:08x}", state.pc);
    for (reg_idx, reg) in state.registers.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.value);
    }

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

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
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    // evaluate memory witness

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

    // let mut permutation_argument_accumulator = produce_pc_into_permutation_accumulator_raw(
    //     INITIAL_PC,
    //     split_timestamp(INITIAL_TIMESTAMP),
    //     final_pc,
    //     split_timestamp(final_timestamp),
    //     &external_challenges
    //         .machine_state_permutation_argument
    //         .as_ref()
    //         .unwrap()
    //         .linearization_challenges,
    //     &external_challenges
    //         .machine_state_permutation_argument
    //         .as_ref()
    //         .unwrap()
    //         .additive_term,
    // );
    // let t = produce_register_contribution_into_memory_accumulator(
    //     &register_final_state,
    //     external_challenges
    //         .memory_argument
    //         .memory_argument_linearization_challenges,
    //     external_challenges.memory_argument.memory_argument_gamma,
    // );
    // permutation_argument_accumulator.mul_assign(&t);

    let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();
    let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();

    write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));
    read_set.insert((final_pc, final_timestamp));

    let mut memory_read_set = BTreeSet::new();
    let mut memory_write_set = BTreeSet::new();

    for i in 0..32 {
        memory_write_set.insert((true, i as u32, 0, 0));
        memory_read_set.insert((
            true,
            i as u32,
            register_final_state[i].last_access_timestamp,
            register_final_state[i].current_value,
        ));
    }

    assert!(
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>() < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );

    if PROVE_ADD_SUB {
        println!("Will try to prove ADD/SUB/LUI/AUIPC/MOP circuit");
        const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

        let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
        dbg!(num_calls);

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

        // let row = 337;
        // dbg!(buffer[row]);
        // dbg!(decoder_table_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);
        // dbg!(witness_gen_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        dbg!(oracle.inner.len());

        let is_empty = oracle.inner.is_empty();

        println!("Computing memory trace");
        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );

        println!("Computing full trace");
        let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            add_sub_lui_auipc_mop::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // parse_state_permutation_elements_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut write_set,
        //     &mut read_set,
        // );
        // parse_shuffle_ram_accesses_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut memory_write_set,
        //     &mut memory_read_set,
        // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&add_sub_circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_24();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    trace_len,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/add_sub_lui_auipc_mop_gkr_proof.json");

            // serialize_to_file_if_not_gpu_comparison(
            //     &proof,
            //     "add_sub_lui_auipc_mop_unrolled_proof.json",
            // );

            // if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
            //     let gpu_comparison_args = GpuComparisonArgs {
            //         circuit: &add_sub_circuit,
            //         setup: &setup,
            //         external_challenges: &external_challenges,
            //         aux_boundary_values: &[],
            //         public_inputs: &vec![],
            //         twiddles: &twiddles,
            //         lde_precomputations: &lde_precomputations,
            //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            //         log_n: TRACE_LEN_LOG2,
            //         circuit_sequence: None,
            //         delegation_processing_type: None,
            //         is_unrolled: true,
            //         prover_data: &prover_data,
            //     };
            //     gpu_comparison_hook(&gpu_comparison_args);
            // }

            // permutation_argument_accumulator
            //     .mul_assign(&proof.permutation_grand_product_accumulator);
        }
    }

    if PROVE_JUMP_BRANCH {
        println!("Will try to prove JUMP/BRANCH/SLT circuit");
        const CIRCUIT_TYPE: u8 = JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/jump_branch_slt_preprocessed_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn(
            &mut table_driver,
        );

        dbg!(table_driver.total_tables_len);

        let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
        dbg!(num_calls);

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

        // let row = 0;
        // dbg!(buffer[row]);
        // dbg!(decoder_table_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);
        // dbg!(witness_gen_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let is_empty = oracle.inner.is_empty();

        println!("Computing memory trace");
        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );

        println!("Computing full trace");
        let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            jump_branch_slt::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // parse_state_permutation_elements_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut write_set,
        //     &mut read_set,
        // );
        // parse_shuffle_ram_accesses_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut memory_write_set,
        //     &mut memory_read_set,
        // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_24();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    trace_len,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/jump_branch_slt_gkr_proof.json");

            // serialize_to_file_if_not_gpu_comparison(
            //     &proof,
            //     "add_sub_lui_auipc_mop_unrolled_proof.json",
            // );

            // if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
            //     let gpu_comparison_args = GpuComparisonArgs {
            //         circuit: &add_sub_circuit,
            //         setup: &setup,
            //         external_challenges: &external_challenges,
            //         aux_boundary_values: &[],
            //         public_inputs: &vec![],
            //         twiddles: &twiddles,
            //         lde_precomputations: &lde_precomputations,
            //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            //         log_n: TRACE_LEN_LOG2,
            //         circuit_sequence: None,
            //         delegation_processing_type: None,
            //         is_unrolled: true,
            //         prover_data: &prover_data,
            //     };
            //     gpu_comparison_hook(&gpu_comparison_args);
            // }

            // permutation_argument_accumulator
            //     .mul_assign(&proof.permutation_grand_product_accumulator);
        }
    }

    if PROVE_SHIFTS_BINOPS {
        println!("Will try to prove SHIFT/BINARY circuit");
        const CIRCUIT_TYPE: u8 = SHIFT_BINARY_CIRCUIT_FAMILY_IDX;

        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/shift_binop_preprocessed_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn(&mut table_driver);

        dbg!(table_driver.total_tables_len);

        let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
        dbg!(num_calls);

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

        // let row = 1;
        // dbg!(buffer[row]);
        // println!(
        //     "Opcode = 0x{:08x}",
        //     text_section[(buffer[row].opcode_data.initial_pc / 4) as usize]
        // );
        // dbg!(decoder_table_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);
        // dbg!(witness_gen_data[(buffer[row].opcode_data.initial_pc / 4) as usize]);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let is_empty = oracle.inner.is_empty();

        println!("Computing memory trace");
        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );

        println!("Computing full trace");
        let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            shift_binary_ops::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // parse_state_permutation_elements_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut write_set,
        //     &mut read_set,
        // );
        // parse_shuffle_ram_accesses_from_full_trace(
        //     &add_sub_circuit,
        //     &full_trace,
        //     &mut memory_write_set,
        //     &mut memory_read_set,
        // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_24();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    trace_len,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/shift_binop_gkr_proof.json");

            // serialize_to_file_if_not_gpu_comparison(
            //     &proof,
            //     "add_sub_lui_auipc_mop_unrolled_proof.json",
            // );

            // if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
            //     let gpu_comparison_args = GpuComparisonArgs {
            //         circuit: &add_sub_circuit,
            //         setup: &setup,
            //         external_challenges: &external_challenges,
            //         aux_boundary_values: &[],
            //         public_inputs: &vec![],
            //         twiddles: &twiddles,
            //         lde_precomputations: &lde_precomputations,
            //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            //         log_n: TRACE_LEN_LOG2,
            //         circuit_sequence: None,
            //         delegation_processing_type: None,
            //         is_unrolled: true,
            //         prover_data: &prover_data,
            //     };
            //     gpu_comparison_hook(&gpu_comparison_args);
            // }

            // permutation_argument_accumulator
            //     .mul_assign(&proof.permutation_grand_product_accumulator);
        }
    }

    // if true {
    //     println!("Will try to prove MUL/DIV circuit");

    //     use crate::cs::machine::ops::unrolled::mul_div::*;

    //     let witness_fn = if SUPPORT_SIGNED {
    //         mul_div::witness_eval_fn
    //     } else {
    //         mul_div_unsigned_only::witness_eval_fn
    //     };

    //     let mul_div_circuit = {
    //         compile_unrolled_circuit_state_transition::<BabyBearField>(
    //             &|cs| {
    //                 mul_div_table_addition_fn(cs);
    //             },
    //             &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, SUPPORT_SIGNED>(cs),
    //             1 << 20,
    //             TRACE_LEN_LOG2,
    //         )
    //     };

    //     let mut table_driver = TableDriver::<BabyBearField>::new();
    //     mul_div_table_driver_fn(&mut table_driver);

    //     let num_calls = counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>();
    //     dbg!(num_calls);

    //     let mut state = snapshotter.initial_snapshot.state;
    //     let mut ram_log_buffers = snapshotter
    //         .reads_buffer
    //         .make_range(0..snapshotter.reads_buffer.len());

    //     let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
    //         ram_log: &mut ram_log_buffers,
    //     };

    //     let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    //     let mut buffers = vec![&mut buffer[..]];
    //     let mut tracer = NonMemDestinationHolder::<MUL_DIV_CIRCUIT_FAMILY_IDX> {
    //         buffers: &mut buffers[..],
    //     };

    //     ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
    //         &mut state,
    //         &mut ram,
    //         &tape,
    //         &mut (),
    //         cycles_bound,
    //         &mut tracer,
    //     );
    //     assert_eq!(expected_final_state, state);

    //     let (decoder_table_data, witness_gen_data) =
    //         &preprocessing_data[&MUL_DIV_CIRCUIT_FAMILY_IDX];
    //     let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

    //     let oracle = NonMemoryCircuitOracle {
    //         inner: &buffer[..],
    //         decoder_table: witness_gen_data,
    //         default_pc_value_in_padding: 4,
    //     };

    //     let is_empty = oracle.inner.is_empty();

    //     let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
    //         &mul_div_circuit,
    //         NUM_CYCLES_PER_CHUNK,
    //         &oracle,
    //         &worker,
    //         Global,
    //     );

    //     let full_trace = evaluate_witness_for_executor_family::<_, Global>(
    //         &mul_div_circuit,
    //         witness_fn,
    //         NUM_CYCLES_PER_CHUNK,
    //         &oracle,
    //         &table_driver,
    //         &worker,
    //         Global,
    //     );

    //     ensure_memory_trace_consistency(&memory_trace, &full_trace);

    //     parse_state_permutation_elements_from_full_trace(
    //         &mul_div_circuit,
    //         &full_trace,
    //         &mut write_set,
    //         &mut read_set,
    //     );
    //     parse_shuffle_ram_accesses_from_full_trace(
    //         &mul_div_circuit,
    //         &full_trace,
    //         &mut memory_write_set,
    //         &mut memory_read_set,
    //     );

    //     if CHECK_MEMORY_PERMUTATION_ONLY == false {
    //         let is_satisfied = check_satisfied(
    //             &mul_div_circuit,
    //             &full_trace.exec_trace,
    //             full_trace.num_witness_columns,
    //         );
    //         assert!(is_satisfied);

    //         let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    //         let lde_precomputations =
    //             LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
    //         let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
    //             &table_driver,
    //             &decoder_table_data,
    //             trace_len,
    //             &mul_div_circuit.setup_layout,
    //             &twiddles,
    //             &lde_precomputations,
    //             lde_factor,
    //             tree_cap_size,
    //             &worker,
    //         );

    //         let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
    //             Some(full_trace.lookup_mapping.clone())
    //         } else {
    //             None
    //         };

    //         println!("Trying to prove");

    //         let now = std::time::Instant::now();
    //         let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
    //             DEFAULT_TRACE_PADDING_MULTIPLE,
    //             _,
    //             DefaultTreeConstructor,
    //         >(
    //             &mul_div_circuit,
    //             &vec![],
    //             &external_challenges,
    //             full_trace,
    //             &[],
    //             &setup,
    //             &twiddles,
    //             &lde_precomputations,
    //             None,
    //             lde_factor,
    //             tree_cap_size,
    //             53,
    //             28,
    //             &worker,
    //         );
    //         println!("Proving time is {:?}", now.elapsed());

    //         if is_empty {
    //             assert_eq!(
    //                 proof.permutation_grand_product_accumulator,
    //                 BabyBearExt4::ONE
    //             );
    //         }
    //         assert!(proof.delegation_argument_accumulator.is_none());

    //         if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
    //             let gpu_comparison_args = GpuComparisonArgs {
    //                 circuit: &mul_div_circuit,
    //                 setup: &setup,
    //                 external_challenges: &external_challenges,
    //                 aux_boundary_values: &[],
    //                 public_inputs: &vec![],
    //                 twiddles: &twiddles,
    //                 lde_precomputations: &lde_precomputations,
    //                 lookup_mapping: lookup_mapping_for_gpu.unwrap(),
    //                 log_n: TRACE_LEN_LOG2,
    //                 circuit_sequence: None,
    //                 delegation_processing_type: None,
    //                 is_unrolled: true,
    //                 prover_data: &prover_data,
    //             };
    //             gpu_comparison_hook(&gpu_comparison_args);
    //         }

    //         if SUPPORT_SIGNED {
    //             serialize_to_file_if_not_gpu_comparison(&proof, "mul_div_unrolled_proof.json");
    //         } else {
    //             serialize_to_file_if_not_gpu_comparison(
    //                 &proof,
    //                 "mul_div_unsigned_unrolled_proof.json",
    //             );
    //         };

    //         permutation_argument_accumulator
    //             .mul_assign(&proof.permutation_grand_product_accumulator);
    //     }
    // }

    if PROVE_MEM_WORD {
        println!("Will try to prove word LOAD/STORE circuit");
        const CIRCUIT_TYPE: u8 = LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;

        // let word_load_store_circuit = {
        //     compile_unrolled_circuit_state_transition::<BabyBearField>(
        //         &|cs| {
        //             word_only_load_store_table_addition_fn(cs);
        //             for (table_type, table) in extra_tables.clone() {
        //                 cs.add_table_with_content(table_type, table);
        //             }
        //         },
        //         &|cs| {
        //             word_only_load_store_circuit_with_preprocessed_bytecode::<
        //                 _,
        //                 _,
        //                 { common_constants::ROM_SECOND_WORD_BITS },
        //             >(cs)
        //         },
        //         1 << 20,
        //         TRACE_LEN_LOG2,
        //     )
        // };
        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/mem_word_only_preprocessed_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(&mut table_driver);
        let extra_tables = cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
            _,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(&binary);
        for (table_type, table) in extra_tables {
            table_driver.add_table_with_content(table_type, table);
        }
        dbg!(table_driver.total_tables_len);

        let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = MemDestinationHolder::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX> {
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

        // let (decoder_table_data, witness_gen_data) =
        //     &preprocessing_data[&LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX];
        // let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);
        let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];
        let witness_gen_data = decoder_table_data
            .iter()
            .map(|el| el.unwrap_or(Default::default()))
            .collect::<Vec<_>>();

        let oracle = MemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
        };

        let is_empty = oracle.inner.is_empty();

        // let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
        //     &word_load_store_circuit,
        //     NUM_CYCLES_PER_CHUNK,
        //     &oracle,
        //     &worker,
        //     Global,
        // );
        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );

        println!("Computing full trace");
        // let full_trace = evaluate_witness_for_executor_family::<_, Global>(
        //     &word_load_store_circuit,
        //     word_load_store::witness_eval_fn,
        //     NUM_CYCLES_PER_CHUNK,
        //     &oracle,
        //     &table_driver,
        //     &worker,
        //     Global,
        // );
        let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            mem_word_only::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // parse_state_permutation_elements_from_full_trace(
        //     &word_load_store_circuit,
        //     &full_trace,
        //     &mut write_set,
        //     &mut read_set,
        // );
        // parse_shuffle_ram_accesses_from_full_trace(
        //     &word_load_store_circuit,
        //     &full_trace,
        //     &mut memory_write_set,
        //     &mut memory_read_set,
        // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // let is_satisfied = check_satisfied(
            //     &word_load_store_circuit,
            //     &full_trace.exec_trace,
            //     full_trace.num_witness_columns,
            // );
            // assert!(is_satisfied);
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
            println!("Preparing setup");
            // let lde_precomputations =
            //     LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
            // let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            //     &table_driver,
            //     &decoder_table_data,
            //     trace_len,
            //     &word_load_store_circuit.setup_layout,
            //     &twiddles,
            //     &lde_precomputations,
            //     lde_factor,
            //     tree_cap_size,
            //     &worker,
            // );
            let setup =
                GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            println!("Trying to prove");

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_24();

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    trace_len,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());
            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/mem_word_only_gkr_proof.json");

            // assert!(proof.delegation_argument_accumulator.is_none());

            // if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
            //     let gpu_comparison_args = GpuComparisonArgs {
            //         circuit: &word_load_store_circuit,
            //         setup: &setup,
            //         external_challenges: &external_challenges,
            //         aux_boundary_values: &[],
            //         public_inputs: &vec![],
            //         twiddles: &twiddles,
            //         lde_precomputations: &lde_precomputations,
            //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            //         log_n: TRACE_LEN_LOG2,
            //         circuit_sequence: None,
            //         delegation_processing_type: None,
            //         is_unrolled: true,
            //         prover_data: &prover_data,
            //     };
            //     gpu_comparison_hook(&gpu_comparison_args);
            // }

            // serialize_to_file_if_not_gpu_comparison(
            //     &proof,
            //     "word_only_load_store_unrolled_proof.json",
            // );

            // permutation_argument_accumulator
            //     .mul_assign(&proof.permutation_grand_product_accumulator);
        }
    }

    if PROVE_MEM_SUBWORD {
        println!("Will try to prove subword LOAD/STORE circuit");
        const CIRCUIT_TYPE: u8 = LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;

        // use cs::machine::ops::unrolled::load_store::*;

        // let extra_tables = create_load_store_special_tables::<
        //     _,
        //     { common_constants::ROM_SECOND_WORD_BITS },
        // >(&binary);
        // let subword_load_store_circuit = {
        //     compile_unrolled_circuit_state_transition::<BabyBearField>(
        //         &|cs| {
        //             subword_only_load_store_table_addition_fn(cs);
        //             for (table_type, table) in extra_tables.clone() {
        //                 cs.add_table_with_content(table_type, table);
        //             }
        //         },
        //         &|cs| {
        //             subword_only_load_store_circuit_with_preprocessed_bytecode::<
        //                 _,
        //                 _,
        //                 { common_constants::ROM_SECOND_WORD_BITS },
        //             >(cs)
        //         },
        //         1 << 20,
        //         TRACE_LEN_LOG2,
        //     )
        // };
        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/mem_subword_only_preprocessed_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(&mut table_driver);
        let extra_tables =
            cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(&binary);
        for (table_type, table) in extra_tables {
            table_driver.add_table_with_content(table_type, table);
        }
        dbg!(table_driver.total_tables_len);

        let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = MemDestinationHolder::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX> {
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

        // let (decoder_table_data, witness_gen_data) =
        //     &preprocessing_data[&LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX];
        // let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);
        let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];
        let witness_gen_data = decoder_table_data
            .iter()
            .map(|el| el.unwrap_or(Default::default()))
            .collect::<Vec<_>>();

        // {
        //     fast_serialize_to_file_if_not_gpu_comparison(&(buffer.clone(), witness_gen_data.clone()), "test_wit.bin");
        // }

        let oracle = MemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
        };

        let is_empty = oracle.inner.is_empty();

        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );

        println!("Computing full trace");
        let full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
            &circuit,
            mem_subword_only::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // parse_state_permutation_elements_from_full_trace(
        //     &subword_load_store_circuit,
        //     &full_trace,
        //     &mut write_set,
        //     &mut read_set,
        // );
        // parse_shuffle_ram_accesses_from_full_trace(
        //     &subword_load_store_circuit,
        //     &full_trace,
        //     &mut memory_write_set,
        //     &mut memory_read_set,
        // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // let is_satisfied = check_satisfied(
            //     &subword_load_store_circuit,
            //     &full_trace.exec_trace,
            //     full_trace.num_witness_columns,
            // );
            // assert!(is_satisfied);
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
            // let lde_precomputations =
            //     LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
            // let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            //     &table_driver,
            //     &decoder_table_data,
            //     trace_len,
            //     &subword_load_store_circuit.setup_layout,
            //     &twiddles,
            //     &lde_precomputations,
            //     lde_factor,
            //     tree_cap_size,
            //     &worker,
            // );
            let setup =
                GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            println!("Trying to prove");

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_24();

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    trace_len,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());
            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/mem_subword_only_gkr_proof.json");

            // assert!(proof.delegation_argument_accumulator.is_none());

            // if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
            //     let gpu_comparison_args = GpuComparisonArgs {
            //         circuit: &subword_load_store_circuit,
            //         setup: &setup,
            //         external_challenges: &external_challenges,
            //         aux_boundary_values: &[],
            //         public_inputs: &vec![],
            //         twiddles: &twiddles,
            //         lde_precomputations: &lde_precomputations,
            //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            //         log_n: TRACE_LEN_LOG2,
            //         circuit_sequence: None,
            //         delegation_processing_type: None,
            //         is_unrolled: true,
            //         prover_data: &prover_data,
            //     };
            //     gpu_comparison_hook(&gpu_comparison_args);
            // }

            // serialize_to_file_if_not_gpu_comparison(
            //     &proof,
            //     "subword_only_load_store_unrolled_proof.json",
            // );

            // permutation_argument_accumulator
            //     .mul_assign(&proof.permutation_grand_product_accumulator);
        }
    }

    // // Machine state permutation ended
    // {
    //     for (pc, ts) in write_set.iter().copied() {
    //         if read_set.contains(&(pc, ts)) == false {
    //             panic!("read set doesn't contain a pair {:?}", (pc, ts));
    //         }
    //     }

    //     for (pc, ts) in read_set.iter().copied() {
    //         if write_set.contains(&(pc, ts)) == false {
    //             panic!("write set doesn't contain a pair {:?}", (pc, ts));
    //         }
    //     }
    // }

    // if true {
    //     println!("Will try to prove memory inits and teardowns circuit");

    //     let compiler = OneRowCompiler::<BabyBearField>::default();
    //     let inits_and_teardowns_circuit =
    //         compiler.compile_init_and_teardown_circuit(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2);

    //     let table_driver = TableDriver::<BabyBearField>::new();

    //     let inits_data = &inits_and_teardowns[0];

    //     let memory_trace = evaluate_init_and_teardown_memory_witness::<Global>(
    //         &inits_and_teardowns_circuit,
    //         NUM_CYCLES_PER_CHUNK,
    //         &inits_data.lazy_init_data,
    //         &worker,
    //         Global,
    //     );

    //     let full_trace = evaluate_init_and_teardown_witness::<Global>(
    //         &inits_and_teardowns_circuit,
    //         NUM_CYCLES_PER_CHUNK,
    //         &inits_data.lazy_init_data,
    //         &worker,
    //         Global,
    //     );

    //     let WitnessEvaluationData {
    //         aux_data,
    //         exec_trace,
    //         num_witness_columns,
    //         lookup_mapping,
    //     } = full_trace;
    //     let full_trace = WitnessEvaluationDataForExecutionFamily {
    //         aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
    //         exec_trace,
    //         num_witness_columns,
    //         lookup_mapping,
    //     };

    //     if CHECK_MEMORY_PERMUTATION_ONLY == false {
    //         let is_satisfied = check_satisfied(
    //             &inits_and_teardowns_circuit,
    //             &full_trace.exec_trace,
    //             full_trace.num_witness_columns,
    //         );
    //         assert!(is_satisfied);

    //         let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    //         let lde_precomputations =
    //             LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
    //         let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
    //             &table_driver,
    //             &[],
    //             trace_len,
    //             &inits_and_teardowns_circuit.setup_layout,
    //             &twiddles,
    //             &lde_precomputations,
    //             lde_factor,
    //             tree_cap_size,
    //             &worker,
    //         );

    //         let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
    //             Some(full_trace.lookup_mapping.clone())
    //         } else {
    //             None
    //         };

    //         println!("Trying to prove");

    //         let now = std::time::Instant::now();
    //         let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
    //             DEFAULT_TRACE_PADDING_MULTIPLE,
    //             _,
    //             DefaultTreeConstructor,
    //         >(
    //             &inits_and_teardowns_circuit,
    //             &vec![],
    //             &external_challenges,
    //             full_trace,
    //             &aux_data.aux_boundary_data,
    //             &setup,
    //             &twiddles,
    //             &lde_precomputations,
    //             None,
    //             lde_factor,
    //             tree_cap_size,
    //             53,
    //             28,
    //             &worker,
    //         );
    //         println!("Proving time is {:?}", now.elapsed());

    //         serialize_to_file_if_not_gpu_comparison(
    //             &proof,
    //             "inits_and_teardowns_unrolled_proof.json",
    //         );

    //         if let Some(ref gpu_comparison_hook) = maybe_gpu_unrolled_comparison_hook {
    //             let gpu_comparison_args = GpuComparisonArgs {
    //                 circuit: &inits_and_teardowns_circuit,
    //                 setup: &setup,
    //                 external_challenges: &external_challenges,
    //                 aux_boundary_values: &aux_data.aux_boundary_data,
    //                 public_inputs: &vec![],
    //                 twiddles: &twiddles,
    //                 lde_precomputations: &lde_precomputations,
    //                 lookup_mapping: lookup_mapping_for_gpu.unwrap(),
    //                 log_n: TRACE_LEN_LOG2,
    //                 circuit_sequence: None,
    //                 delegation_processing_type: None,
    //                 is_unrolled: true,
    //                 prover_data: &prover_data,
    //             };
    //             gpu_comparison_hook(&gpu_comparison_args);
    //         }

    //         permutation_argument_accumulator
    //             .mul_assign(&proof.permutation_grand_product_accumulator);
    //     }
    // }

    // now prove delegation circuits
    if PROVE_BLAKE {
        println!("Will try to prove Blake delegation");

        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(&mut table_driver);

        dbg!(table_driver.total_tables_len);

        let num_calls = counters.blake_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BlakeDelegationDestinationHolder {
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

        // evaluate a witness and memory-only witness for each

        let delegation_type = BLAKE2S_DELEGATION_CSR_REGISTER as u16;
        let oracle = Blake2sDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };

        let is_empty = oracle.cycle_data.is_empty();

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating memory-only witness for delegation circuit {}",
            delegation_type
        );
        let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
            &circuit,
            BLAKE_NUM_DELEGATION_CYCLES,
            &oracle,
            &worker,
            Global,
            Global,
        );

        let eval_fn = super::blake2_with_extended_control::witness_eval_fn;

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating witness for delegation circuit {}",
            delegation_type
        );
        let full_trace = evaluate_gkr_witness_for_delegation_circuit(
            &circuit,
            eval_fn,
            BLAKE_NUM_DELEGATION_CYCLES,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // // parse_delegation_ram_accesses_from_full_trace(
        // //     &circuit,
        // //     &full_witness,
        // //     &mut memory_write_set,
        // //     &mut memory_read_set,
        // // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> = Twiddles::new(BLAKE_NUM_DELEGATION_CYCLES, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &[], BLAKE_NUM_DELEGATION_CYCLES, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                BLAKE_NUM_DELEGATION_CYCLES.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_20();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    BLAKE_NUM_DELEGATION_CYCLES,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(
                &proof,
                "test_proofs/blake2_with_extended_control_gkr_proof.json",
            );
        }
    }

    if PROVE_BIGINT {
        println!("Will try to prove Bigint delegation");

        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json",
            )
        };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(&mut table_driver);

        dbg!(table_driver.total_tables_len);

        let num_calls = counters.bigint_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BigintDelegationDestinationHolder {
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

        // evaluate a witness and memory-only witness for each

        let delegation_type = BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16;
        let oracle = BigintDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };

        let is_empty = oracle.cycle_data.is_empty();

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating memory-only witness for delegation circuit {}",
            delegation_type
        );
        let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
            &circuit,
            BIGINT_NUM_DELEGATION_CYCLES,
            &oracle,
            &worker,
            Global,
            Global,
        );

        let eval_fn = super::bigint_with_extended_control::witness_eval_fn;

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating witness for delegation circuit {}",
            delegation_type
        );
        let full_trace = evaluate_gkr_witness_for_delegation_circuit(
            &circuit,
            eval_fn,
            BIGINT_NUM_DELEGATION_CYCLES,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // // parse_delegation_ram_accesses_from_full_trace(
        // //     &circuit,
        // //     &full_witness,
        // //     &mut memory_write_set,
        // //     &mut memory_read_set,
        // // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> =
                Twiddles::new(BIGINT_NUM_DELEGATION_CYCLES, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &[], BIGINT_NUM_DELEGATION_CYCLES, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                BIGINT_NUM_DELEGATION_CYCLES.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_22();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    BIGINT_NUM_DELEGATION_CYCLES,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(
                &proof,
                "test_proofs/bigint_with_extended_control_gkr_proof.json",
            );
        }
    }

    if PROVE_KECCAK {
        println!("Will try to prove Keccak delegation");

        let circuit: GKRCircuitArtifact<BabyBearField> =
            { deserialize_from_file("../cs/compiled_circuits/keccak_special5_layout_gkr.json") };

        let mut table_driver = TableDriver::<BabyBearField>::new();
        cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(&mut table_driver);

        dbg!(table_driver.total_tables_len);
        dbg!(table_driver.max_table_width());

        let num_calls = counters.keccak_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = KeccakDelegationDestinationHolder {
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

        // evaluate a witness and memory-only witness for each

        let delegation_type = KECCAK_SPECIAL5_CSR_REGISTER as u16;
        let oracle = KeccakDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };

        let is_empty = oracle.cycle_data.is_empty();

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating memory-only witness for delegation circuit {}",
            delegation_type
        );
        let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
            &circuit,
            KECCAK_NUM_DELEGATION_CYCLES,
            &oracle,
            &worker,
            Global,
            Global,
        );

        let eval_fn = super::keccak_special5::witness_eval_fn;

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating witness for delegation circuit {}",
            delegation_type
        );
        let full_trace = evaluate_gkr_witness_for_delegation_circuit(
            &circuit,
            eval_fn,
            KECCAK_NUM_DELEGATION_CYCLES,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        // // parse_delegation_ram_accesses_from_full_trace(
        // //     &circuit,
        // //     &full_witness,
        // //     &mut memory_write_set,
        // //     &mut memory_read_set,
        // // );

        if CHECK_MEMORY_PERMUTATION_ONLY == false {
            // println!("Will check constraints satisfiability");
            // let is_satisfied = check_satisfied(&circuit, &full_trace);
            // assert!(is_satisfied);

            println!("Preparing twiddles");
            let twiddles: Twiddles<_, Global> =
                Twiddles::new(KECCAK_NUM_DELEGATION_CYCLES, &worker);
            println!("Preparing setup");
            let setup =
                GKRSetup::construct(&table_driver, &[], KECCAK_NUM_DELEGATION_CYCLES, &circuit);

            let setup_commitment = setup.commit(
                &twiddles,
                2,
                1,
                tree_cap_size,
                KECCAK_NUM_DELEGATION_CYCLES.trailing_zeros() as usize,
                &worker,
            );

            // let lookup_mapping_for_gpu = if maybe_gpu_unrolled_comparison_hook.is_some() {
            //     Some(full_trace.lookup_mapping.clone())
            // } else {
            //     None
            // };

            let whir_schedule = WhirSchedule::default_for_tests_80_bits_22();

            println!("Trying to prove");

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &circuit,
                    &external_challenges,
                    full_trace,
                    &setup,
                    &setup_commitment,
                    &twiddles,
                    &whir_schedule,
                    None,
                    KECCAK_NUM_DELEGATION_CYCLES,
                    &worker,
                );
            println!("Proving time is {:?}", now.elapsed());

            println!(
                "Estimated proof size without compression is {} bytes",
                proof.estimate_size()
            );

            if is_empty {
                assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
            }

            serialize_to_file(&proof, "test_proofs/keccak_special5_gkr_proof.json");
        }
    }

    // dbg!(permutation_argument_accumulator);
    // dbg!(delegation_argument_accumulator);

    // // inits and teardowns
    // {
    //     let expected_init_set: Vec<_> = memory_read_set.difference(&memory_write_set).collect();
    //     let expected_teardown_set: Vec<_> = memory_write_set.difference(&memory_read_set).collect();
    //     assert_eq!(expected_init_set.len(), expected_teardown_set.len());
    //     // assert_eq!(expected_init_set.len(), flattened_inits_and_teardowns.len());

    //     if flattened_inits_and_teardowns.len() != expected_init_set.len() {
    //         for (idx, (address, (teardown_ts, teardown_value))) in
    //             flattened_inits_and_teardowns.iter().enumerate()
    //         {
    //             let mut init_set_el = None;
    //             for (i, (is_reg, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
    //                 if *addr == *address {
    //                     init_set_el = Some((*is_reg, *addr, *ts, *init_value));
    //                 }
    //             }
    //             let Some(init_set_el) = init_set_el else {
    //                 panic!("No expected init set element for address {} of flattened inits or teardowns", *address);
    //             };

    //             let mut teardown_set_el = None;
    //             for (i, (is_reg, addr, ts, teardown_value)) in
    //                 expected_teardown_set.iter().enumerate()
    //             {
    //                 if *addr == *address {
    //                     teardown_set_el = Some((*is_reg, *addr, *ts, *teardown_value));
    //                 }
    //             }
    //             let Some(teardown_set_el) = teardown_set_el else {
    //                 panic!("No expected teardown set element for address {} of flattened inits or teardowns", *address);
    //             };
    //             let (_, _, expected_teardown_ts, expected_teardown_value) = teardown_set_el;
    //             assert_eq!(
    //                 *teardown_ts, expected_teardown_ts,
    //                 "failed for address {}",
    //                 address
    //             );
    //             assert_eq!(
    //                 *teardown_value, expected_teardown_value,
    //                 "failed for address {}",
    //                 address
    //             );
    //         }
    //     }

    //     for (idx, (is_register, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
    //         assert!(
    //             *is_register == false,
    //             "found an unexpected init for register {} with value {} at timestamp {}",
    //             *addr,
    //             *init_value,
    //             *ts
    //         );
    //         assert_eq!(
    //             *ts, 0,
    //             "init timestamp is invalid for memory address {}",
    //             addr
    //         );
    //         assert_eq!(
    //             *init_value, 0,
    //             "init value is invalid for memory address {}",
    //             addr
    //         );
    //         assert_eq!(
    //             flattened_inits_and_teardowns[idx].0, *addr,
    //             "diverged at expected lazy init {}",
    //             idx
    //         );
    //     }
    //     for (idx, (is_register, addr, ts, value)) in expected_teardown_set.iter().enumerate() {
    //         assert!(
    //             *is_register == false,
    //             "found an unexpected teardown for register {} with value {} at timestamp {}",
    //             *addr,
    //             *value,
    //             *ts
    //         );
    //         assert!(
    //             *ts > INITIAL_TIMESTAMP,
    //             "teardown timestamp is invalid for memory address {}",
    //             addr
    //         );
    //         assert_eq!(
    //             flattened_inits_and_teardowns[idx].1 .0, *ts,
    //             "diverged at expected lazy init {}",
    //             idx
    //         );
    //         assert_eq!(
    //             flattened_inits_and_teardowns[idx].1 .1, *value,
    //             "diverged at expected lazy init {}",
    //             idx
    //         );
    //     }

    //     for ((_, addr0, _, _), (_, addr1, _, _)) in
    //         expected_init_set.iter().zip(expected_teardown_set.iter())
    //     {
    //         assert_eq!(*addr0, *addr1);
    //     }

    //     assert_eq!(total_unique_teardowns, expected_teardown_set.len());
    // }

    // assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);
    // assert_eq!(delegation_argument_accumulator, BabyBearExt4::ZERO);
}
