use super::*;
use crate::tests::unrolled::word_specialized::*;
use riscv_transpiler::replayer::*;
use std::collections::BTreeSet;

use risc_v_simulator::machine_mode_only_unrolled::*;
use riscv_transpiler::witness::*;

use cs::definitions::INITIAL_TIMESTAMP;
use cs::machine::ops::unrolled::{
    load_store_subword_only::{
        subword_only_load_store_circuit_with_preprocessed_bytecode,
        subword_only_load_store_table_addition_fn, subword_only_load_store_table_driver_fn,
    },
    load_store_word_only::{
        create_word_only_load_store_special_tables,
        word_only_load_store_circuit_with_preprocessed_bytecode,
        word_only_load_store_table_addition_fn, word_only_load_store_table_driver_fn,
    },
};

use crate::unrolled::{
    evaluate_init_and_teardown_memory_witness, evaluate_init_and_teardown_witness,
};

use crate::tracers::oracles::transpiler_oracles::delegation::*;

const SUPPORT_SIGNED: bool = false;
const INITIAL_PC: u32 = 0;
const NUM_INIT_AND_TEARDOWN_SETS: usize = 16;
const NUM_DELEGATION_CYCLES: usize = (1 << 20) - 1;

// #[ignore = "test has explicit panic inside"]
#[test]
fn run_basic_unrolled_test_in_transpiler_with_word_specialization() {
    run_basic_unrolled_test_in_transpiler_with_word_specialization_impl(None);
}

pub fn run_basic_unrolled_test_in_transpiler_with_word_specialization_impl(
    maybe_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>,
) {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;

    type CountersT = DelegationsAndFamiliesCounters;

    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = (1 << TRACE_LEN_LOG2) - 1;

    const SECOND_WORD_BITS: usize = 4;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    // let worker = Worker::new_with_num_threads(1);
    let worker = Worker::new_with_num_threads(8);
    // load binary

    // let binary = std::fs::read("../examples/basic_fibonacci/app.bin").unwrap();
    let binary = std::fs::read("../examples/hashed_fibonacci/app.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section = std::fs::read("../examples/basic_fibonacci/app.text").unwrap();
    let text_section = std::fs::read("../examples/hashed_fibonacci/app.text").unwrap();
    assert!(text_section.len() % 4 == 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // first run to capture minimal information
    let instructions: Vec<Instruction> = text_section
        .iter()
        .copied()
        .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
        .collect();
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<SECOND_WORD_BITS>::from_rom_content(&binary, 1 << 30);
    let period = 1 << 20;
    let num_snapshots = 1;
    let cycles_bound = period * num_snapshots;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, SECOND_WORD_BITS>,
        RamWithRomRegion<SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        num_snapshots,
        &mut ram,
        &mut snapshotter,
        &tape,
        period,
        &mut non_determinism,
    );
    assert!(is_program_finished); // check that we reached looping state (ie. end state for our vm)

    let total_snapshots = snapshotter.snapshots.len();
    let cycles_upper_bound = total_snapshots * period;

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    use crate::tracers::oracles::chunk_lazy_init_and_teardown;
    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
        1,
        NUM_CYCLES_PER_CHUNK * NUM_INIT_AND_TEARDOWN_SETS,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    println!("Finished at PC = 0x{:08x}", state.pc);
    for (reg_idx, reg) in state.registers.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.value);
    }

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

    // for (k, v) in family_circuits.iter() {
    //     println!(
    //         "Traced {} circuits of type {}, total len: {}",
    //         v.len(),
    //         k,
    //         v.iter().map(|el| el.data.len()).sum::<usize>()
    //     );
    // }

    // println!(
    //     "Traced {} word-sized memory circuits, total len {}",
    //     word_mem_circuits.len(),
    //     word_mem_circuits
    //         .iter()
    //         .map(|el| el.data.len())
    //         .sum::<usize>()
    // );
    // println!(
    //     "Traced {} subword-sized memory circuits, total len {}",
    //     subword_mem_circuits.len(),
    //     subword_mem_circuits
    //         .iter()
    //         .map(|el| el.data.len())
    //         .sum::<usize>()
    // );

    let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(2),
        Mersenne31Field(5),
        Mersenne31Field(42),
        Mersenne31Field(123),
    ]);
    let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(11),
        Mersenne31Field(7),
        Mersenne31Field(1024),
        Mersenne31Field(8000),
    ]);

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(5),
        Mersenne31Field(8),
        Mersenne31Field(32),
        Mersenne31Field(16),
    ]);
    let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(200),
        Mersenne31Field(100),
        Mersenne31Field(300),
        Mersenne31Field(400),
    ]);

    let state_permutation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(41),
        Mersenne31Field(42),
        Mersenne31Field(43),
        Mersenne31Field(44),
    ]);
    let state_permutation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(80),
        Mersenne31Field(90),
        Mersenne31Field(100),
        Mersenne31Field(110),
    ]);

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    let external_challenges = ExternalChallenges {
        memory_argument: ExternalMemoryArgumentChallenges {
            memory_argument_linearization_challenges:
                memory_argument_linearization_challenges_powers,
            memory_argument_gamma,
        },
        delegation_argument: Some(ExternalDelegationArgumentChallenges {
            delegation_argument_linearization_challenges,
            delegation_argument_gamma,
        }),
        machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
            linearization_challenges,
            additive_term: state_permutation_argument_gamma,
        }),
    };

    // evaluate memory witness
    use crate::cs::machine::ops::unrolled::process_binary_into_separate_tables;

    let preprocessing_data = if SUPPORT_SIGNED {
        process_binary_into_separate_tables::<Mersenne31Field, Global>(
            &text_section,
            &opcodes_for_full_machine_with_mem_word_access_specialization(),
            1 << 20,
            &[
                NON_DETERMINISM_CSR,
                BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
                KECCAK_SPECIAL5_CSR_REGISTER as u16
            ],
        )
    } else {
        process_binary_into_separate_tables::<Mersenne31Field, Global>(
            &text_section,
            &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
            1 << 20,
            &[
                NON_DETERMINISM_CSR,
                BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
                KECCAK_SPECIAL5_CSR_REGISTER as u16
            ],
        )
    };

    let mut delegation_argument_accumulator = Mersenne31Quartic::ZERO;

    let mut permutation_argument_accumulator = produce_pc_into_permutation_accumulator_raw(
        INITIAL_PC,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .additive_term,
    );
    let t = produce_register_contribution_into_memory_accumulator(
        &register_final_state,
        external_challenges
            .memory_argument
            .memory_argument_linearization_challenges,
        external_challenges.memory_argument.memory_argument_gamma,
    );
    permutation_argument_accumulator.mul_assign(&t);

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
        counters.get_calls_to_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>()
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

    if true {
        println!("Will try to prove ADD/SUB/LUI/AUIPC/MOP circuit");

        let add_sub_circuit = {
            use crate::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
                &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let num_calls =
            counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[9].opcode_data.opcode
        // );
        // dbg!(family_data[0].data[9]);

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &add_sub_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &add_sub_circuit,
            add_sub_lui_auipc_mod::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &TableDriver::new(),
            &worker,
            Global,
        );

        // let mut trace = full_trace.exec_trace.row_view(0..family_data[0].data.len());
        // for _ in 0..family_data[0].data.len() {
        //     unsafe {
        //         let (_, memory) = trace.current_row_split(full_trace.num_witness_columns);
        //         dbg!(&*memory);
        //     }
        // }

        parse_state_permutation_elements_from_full_trace(
            &add_sub_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &add_sub_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &add_sub_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &TableDriver::new(),
            &decoder_table_data,
            trace_len,
            &add_sub_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &add_sub_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());

        serialize_to_file(&proof, "add_sub_lui_auipc_mop_unrolled_proof.json");

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    if true {
        println!("Will try to prove JUMP/BRANCH/SLT circuit");

        use crate::cs::machine::ops::unrolled::jump_branch_slt::*;

        let jump_branch_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| jump_branch_slt_table_addition_fn(cs),
                &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        jump_branch_slt_table_driver_fn(&mut table_driver);

        let num_calls =
            counters.get_calls_to_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 0,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[4].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &jump_branch_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &jump_branch_circuit,
            jump_branch_slt::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        parse_state_permutation_elements_from_full_trace(
            &jump_branch_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &jump_branch_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &jump_branch_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &jump_branch_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &jump_branch_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());

        serialize_to_file(&proof, "jump_branch_slt_unrolled_proof.json");

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        &[BLAKE2S_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER],
        TableType::SpecialCSRProperties.to_table_id(),
    );

    if true {
        println!("Will try to prove XOR/AND/OR/SHIFT/CSR circuit");
        use crate::cs::machine::ops::unrolled::shift_binary_csr::*;

        let shift_binop_csrrw_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    shift_binop_csrrw_table_addition_fn(cs);
                    // and we need to add CSR table
                    cs.add_table_with_content(
                        TableType::SpecialCSRProperties,
                        LookupWrapper::Dimensional3(csr_table.clone()),
                    );
                },
                &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode::<_, _>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        shift_binop_csrrw_table_driver_fn(&mut table_driver);
        table_driver.add_table_with_content(
            TableType::SpecialCSRProperties,
            LookupWrapper::Dimensional3(csr_table),
        );

        let num_calls =
            counters.get_calls_to_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[2].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &shift_binop_csrrw_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &shift_binop_csrrw_circuit,
            shift_binop_csrrw::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        parse_state_permutation_elements_from_full_trace(
            &shift_binop_csrrw_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &shift_binop_csrrw_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &shift_binop_csrrw_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &shift_binop_csrrw_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &shift_binop_csrrw_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
            assert_eq!(
                proof.delegation_argument_accumulator.unwrap(),
                Mersenne31Quartic::ZERO
            );
        }

        serialize_to_file(&proof, "shift_binop_csrrw_unrolled_proof.json");

        dbg!(proof.delegation_argument_accumulator.unwrap());

        delegation_argument_accumulator.add_assign(&proof.delegation_argument_accumulator.unwrap());
        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    if true {
        println!("Will try to prove MUL/DIV circuit");

        use crate::cs::machine::ops::unrolled::mul_div::*;

        let witness_fn = if SUPPORT_SIGNED {
            mul_div::witness_eval_fn
        } else {
            mul_div_unsigned_only::witness_eval_fn
        };

        let mul_div_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    mul_div_table_addition_fn(cs);
                },
                &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, SUPPORT_SIGNED>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        mul_div_table_driver_fn(&mut table_driver);

        let num_calls = counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<MUL_DIV_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&MUL_DIV_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[26].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &mul_div_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &mul_div_circuit,
            witness_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        parse_state_permutation_elements_from_full_trace(
            &mul_div_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &mul_div_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &mul_div_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &mul_div_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &mul_div_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());

        if SUPPORT_SIGNED {
            serialize_to_file(&proof, "mul_div_unrolled_proof.json");
        } else {
            serialize_to_file(&proof, "mul_div_unsigned_unrolled_proof.json");
        };

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    if true {
        println!("Will try to prove word LOAD/STORE circuit");

        let extra_tables =
            create_word_only_load_store_special_tables::<_, SECOND_WORD_BITS>(&binary);
        let word_load_store_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    word_only_load_store_table_addition_fn(cs);
                    for (table_type, table) in extra_tables.clone() {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    word_only_load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(
                        cs,
                    )
                },
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        word_only_load_store_table_driver_fn(&mut table_driver);
        for (table_type, table) in extra_tables.clone() {
            table_driver.add_table_with_content(table_type, table);
        }

        let num_calls =
            counters.get_calls_to_circuit_family::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = MemDestinationHolder::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = MemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[203].opcode_data.opcode
        // );
        // dbg!(family_data[0].data[203].as_load_data());

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &word_load_store_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &word_load_store_circuit,
            word_load_store::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        parse_state_permutation_elements_from_full_trace(
            &word_load_store_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &word_load_store_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &word_load_store_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &word_load_store_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &word_load_store_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());

        serialize_to_file(&proof, "word_only_load_store_unrolled_proof.json");

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    if true {
        println!("Will try to prove subword LOAD/STORE circuit");

        use cs::machine::ops::unrolled::load_store::*;
        const SECOND_WORD_BITS: usize = 4;

        let extra_tables = create_load_store_special_tables::<_, SECOND_WORD_BITS>(&binary);
        let subword_load_store_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    subword_only_load_store_table_addition_fn(cs);
                    for (table_type, table) in extra_tables.clone() {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    subword_only_load_store_circuit_with_preprocessed_bytecode::<
                        _,
                        _,
                        SECOND_WORD_BITS,
                    >(cs)
                },
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        subword_only_load_store_table_driver_fn(&mut table_driver);
        for (table_type, table) in extra_tables.clone() {
            table_driver.add_table_with_content(table_type, table);
        }

        let num_calls =
            counters.get_calls_to_circuit_family::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>();
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = MemDestinationHolder::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = MemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: witness_gen_data,
        };

        let is_empty = oracle.inner.is_empty();

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[29].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &subword_load_store_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &subword_load_store_circuit,
            subword_load_store::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        parse_state_permutation_elements_from_full_trace(
            &subword_load_store_circuit,
            &full_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &subword_load_store_circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &subword_load_store_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &subword_load_store_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &subword_load_store_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());

        serialize_to_file(&proof, "subword_only_load_store_unrolled_proof.json");

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    // Machine state permutation ended
    {
        for (pc, ts) in write_set.iter().copied() {
            if read_set.contains(&(pc, ts)) == false {
                panic!("read set doesn't contain a pair {:?}", (pc, ts));
            }
        }

        for (pc, ts) in read_set.iter().copied() {
            if write_set.contains(&(pc, ts)) == false {
                panic!("write set doesn't contain a pair {:?}", (pc, ts));
            }
        }
    }

    if true {
        println!("Will try to prove memory inits and teardowns circuit");

        let compiler = OneRowCompiler::<Mersenne31Field>::default();
        let inits_and_teardowns_circuit =
            compiler.compile_init_and_teardown_circuit(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2);

        let table_driver = TableDriver::<Mersenne31Field>::new();

        let inits_data = &inits_and_teardowns[0];

        let memory_trace = evaluate_init_and_teardown_memory_witness::<Global>(
            &inits_and_teardowns_circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_data.lazy_init_data,
            &worker,
            Global,
        );

        let full_trace = evaluate_init_and_teardown_witness::<Global>(
            &inits_and_teardowns_circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_data.lazy_init_data,
            &worker,
            Global,
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = full_trace;
        let full_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        let is_satisfied = check_satisfied(
            &inits_and_teardowns_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &[],
            trace_len,
            &inits_and_teardowns_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &inits_and_teardowns_circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &aux_data.aux_boundary_data,
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        serialize_to_file(&proof, "inits_and_teardowns_unrolled_proof.json");

        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);
    }

    // now prove delegation circuits
    if true {
        let mut external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: Default::default(),
        };
        external_values.aux_boundary_values = Default::default();

        let (circuit, table_driver) = {
            use crate::cs::cs::cs_reference::BasicAssembly;
            use cs::delegation::blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit;
            let mut cs = BasicAssembly::<Mersenne31Field>::new();
            define_blake2_with_extended_control_delegation_circuit(&mut cs);
            let (circuit_output, _) = cs.finalize();
            let table_driver = circuit_output.table_driver.clone();
            let compiler = OneRowCompiler::default();
            let circuit = compiler.compile_to_evaluate_delegations(
                circuit_output,
                (NUM_DELEGATION_CYCLES + 1).trailing_zeros() as usize,
            );

            (circuit, table_driver)
        };

        println!("Will try to prove Blake delegation");

        let num_calls = counters.blake_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BlakeDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        // evaluate a witness and memory-only witness for each

        let delegation_type = BLAKE2S_DELEGATION_CSR_REGISTER as u16;
        let oracle = Blake2sDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating memory-only witness for delegation circuit {}",
            delegation_type
        );
        let mem_only_witness = evaluate_delegation_memory_witness(
            &circuit,
            NUM_DELEGATION_CYCLES,
            &oracle,
            &worker,
            Global,
        );

        let eval_fn = super::blake2s_delegation_with_transpiler::witness_eval_fn;

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating witness for delegation circuit {}",
            delegation_type
        );
        let full_witness = evaluate_witness(
            &circuit,
            eval_fn,
            NUM_DELEGATION_CYCLES,
            &oracle,
            &[],
            &table_driver,
            0,
            &worker,
            Global,
        );

        parse_delegation_ram_accesses_from_full_trace(
            &circuit,
            &full_witness,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &circuit,
            &full_witness.exec_trace,
            full_witness.num_witness_columns,
        );
        assert!(is_satisfied);

        let trace_len = NUM_DELEGATION_CYCLES + 1;

        // create setup
        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);

        let setup = SetupPrecomputations::from_tables_and_trace_len(
            &table_driver,
            NUM_DELEGATION_CYCLES + 1,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegated_gpu_comparison_hook.is_some() {
        //     Some(witness.witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
            &circuit,
            &[],
            &external_values,
            full_witness,
            &setup,
            &twiddles,
            &lde_precomputations,
            0,
            Some(delegation_type),
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!(
            "Delegation circuit type {} proving time is {:?}",
            delegation_type,
            now.elapsed()
        );

        // if let Some(ref gpu_comparison_hook) = maybe_delegated_gpu_comparison_hook {
        //     let log_n = work_type.trace_len.trailing_zeros();
        //     assert_eq!(work_type.trace_len, 1 << log_n);
        //     let dummy_public_inputs = Vec::<Mersenne31Field>::new();
        //     let gpu_comparison_args = GpuComparisonArgs {
        //         circuit: &work_type.compiled_circuit,
        //         setup: &setup,
        //         external_values: &external_values,
        //         public_inputs: &dummy_public_inputs,
        //         twiddles: &twiddles,
        //         lde_precomputations: &lde_precomputations,
        //         table_driver: &work_type.table_driver,
        //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
        //         log_n: log_n as usize,
        //         circuit_sequence: 0,
        //         delegation_processing_type: Some(delegation_type),
        //         prover_data: &prover_data,
        //     };
        //     gpu_comparison_hook(&gpu_comparison_args);
        // }

        // if !for_gpu_comparison {
        //     serialize_to_file(&proof, "blake2s_delegator_proof");
        // }

        dbg!(prover_data.stage_2_result.grand_product_accumulator);
        dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

        permutation_argument_accumulator.mul_assign(&proof.memory_grand_product_accumulator);
        delegation_argument_accumulator.sub_assign(&proof.delegation_argument_accumulator.unwrap());
    }

    if true {
        let mut external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: Default::default(),
        };
        external_values.aux_boundary_values = Default::default();

        let (circuit, table_driver) = {
            use crate::cs::cs::cs_reference::BasicAssembly;
            use cs::delegation::keccak_special5::define_keccak_special5_delegation_circuit;
            let mut cs = BasicAssembly::<Mersenne31Field>::new();
            define_keccak_special5_delegation_circuit(&mut cs);
            let (circuit_output, _) = cs.finalize();
            let table_driver = circuit_output.table_driver.clone();
            let compiler = OneRowCompiler::default();
            let circuit = compiler.compile_to_evaluate_delegations(
                circuit_output,
                (NUM_DELEGATION_CYCLES + 1).trailing_zeros() as usize,
            );

            (circuit, table_driver)
        };

        println!("Will try to prove Keccak delegation");

        let num_calls = counters.keccak_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &snapshotter.reads_buffer,
        };
        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };
        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = KeccakDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );

        // evaluate a witness and memory-only witness for each

        let delegation_type = KECCAK_SPECIAL5_CSR_REGISTER as u16;
        let oracle = KeccakDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating memory-only witness for delegation circuit {}",
            delegation_type
        );
        let mem_only_witness = evaluate_delegation_memory_witness(
            &circuit,
            NUM_DELEGATION_CYCLES,
            &oracle,
            &worker,
            Global,
        );

        let eval_fn = super::keccak_special5_delegation_with_transpiler::witness_eval_fn;

        #[cfg(feature = "debug_logs")]
        println!(
            "Evaluating witness for delegation circuit {}",
            delegation_type
        );
        let full_witness = evaluate_witness(
            &circuit,
            eval_fn,
            NUM_DELEGATION_CYCLES,
            &oracle,
            &[],
            &table_driver,
            0,
            &worker,
            Global,
        );

        parse_delegation_ram_accesses_from_full_trace(
            &circuit,
            &full_witness,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        let is_satisfied = check_satisfied(
            &circuit,
            &full_witness.exec_trace,
            full_witness.num_witness_columns,
        );
        assert!(is_satisfied);

        let trace_len = NUM_DELEGATION_CYCLES + 1;

        // create setup
        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);

        let setup = SetupPrecomputations::from_tables_and_trace_len(
            &table_driver,
            NUM_DELEGATION_CYCLES + 1,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegated_gpu_comparison_hook.is_some() {
        //     Some(witness.witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
            &circuit,
            &[],
            &external_values,
            full_witness,
            &setup,
            &twiddles,
            &lde_precomputations,
            0,
            Some(delegation_type),
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!(
            "Delegation circuit type {} proving time is {:?}",
            delegation_type,
            now.elapsed()
        );

        // if let Some(ref gpu_comparison_hook) = maybe_delegated_gpu_comparison_hook {
        //     let log_n = work_type.trace_len.trailing_zeros();
        //     assert_eq!(work_type.trace_len, 1 << log_n);
        //     let dummy_public_inputs = Vec::<Mersenne31Field>::new();
        //     let gpu_comparison_args = GpuComparisonArgs {
        //         circuit: &work_type.compiled_circuit,
        //         setup: &setup,
        //         external_values: &external_values,
        //         public_inputs: &dummy_public_inputs,
        //         twiddles: &twiddles,
        //         lde_precomputations: &lde_precomputations,
        //         table_driver: &work_type.table_driver,
        //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
        //         log_n: log_n as usize,
        //         circuit_sequence: 0,
        //         delegation_processing_type: Some(delegation_type),
        //         prover_data: &prover_data,
        //     };
        //     gpu_comparison_hook(&gpu_comparison_args);
        // }

        // if !for_gpu_comparison {
        //     serialize_to_file(&proof, "keccak_delegator_proof");
        // }

        dbg!(prover_data.stage_2_result.grand_product_accumulator);
        dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

        permutation_argument_accumulator.mul_assign(&proof.memory_grand_product_accumulator);
        delegation_argument_accumulator.sub_assign(&proof.delegation_argument_accumulator.unwrap());
    }

    dbg!(permutation_argument_accumulator);
    dbg!(delegation_argument_accumulator);

    // inits and teardowns
    {
        let expected_init_set: Vec<_> = memory_read_set.difference(&memory_write_set).collect();
        let expected_teardown_set: Vec<_> = memory_write_set.difference(&memory_read_set).collect();
        assert_eq!(expected_init_set.len(), expected_teardown_set.len());

        for (is_register, addr, ts, init_value) in expected_init_set.iter() {
            assert!(*is_register == false);
            assert_eq!(
                *ts, 0,
                "init timestamp is invalid for memory address {}",
                addr
            );
            assert_eq!(
                *init_value, 0,
                "init value is invalid for memory address {}",
                addr
            );
        }
        for (is_register, addr, ts, _) in expected_teardown_set.iter() {
            assert!(*is_register == false);
            assert!(
                *ts > INITIAL_TIMESTAMP,
                "teardown timestamp is invalid for memory address {}",
                addr
            );
        }

        for ((_, addr0, _, _), (_, addr1, _, _)) in
            expected_init_set.iter().zip(expected_teardown_set.iter())
        {
            assert_eq!(*addr0, *addr1);
        }

        assert_eq!(total_unique_teardowns, expected_teardown_set.len());
    }

    assert_eq!(permutation_argument_accumulator, Mersenne31Quartic::ONE);
    assert_eq!(delegation_argument_accumulator, Mersenne31Quartic::ZERO);
}
