use crate::allocator::tracker::AllocationPlacement;
use crate::circuit_type::UnrolledNonMemoryCircuitType;
use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::field::{BF, E4};
use crate::prover::context::{ProverContext, ProverContextConfig};
use crate::witness::memory_unrolled::{
    generate_memory_and_witness_values_unrolled_non_memory,
    generate_memory_values_unrolled_non_memory,
};
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_multiplicities, LookupExpressions,
};
use crate::witness::trace_unrolled::UnrolledNonMemoryTraceDevice;
use crate::witness::witness_unrolled::generate_witness_values_unrolled_non_memory;
use cs::definitions::*;
use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::{
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
    add_sub_lui_auipc_mop_table_addition_fn,
};
use cs::machine::ops::unrolled::{
    compile_unrolled_circuit_state_transition_into_gkr,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    process_binary_into_separate_tables_ext,
};
use cs::tables::TableDriver;
use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use fft::{materialize_powers_serial_starting_with_elem, Twiddles};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, PrimeField};
use itertools::Itertools;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::prover::{prove_configured_with_gkr, GKRExternalChallenges, WhirSchedule};
use prover::gkr::witness_gen::family_circuits::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
use prover::merkle_trees::DefaultTreeConstructor;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::RamShuffleMemStateRecord;
use riscv_transpiler::ir::{preprocess_bytecode, FullUnsignedMachineDecoderConfig, Instruction};
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, RamWithRomRegion, ReplayBuffer, SimpleSnapshotter,
    SimpleTape, State, VM,
};
use riscv_transpiler::witness::NonMemDestinationHolder;
use serial_test::serial;
use setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS;
use std::alloc::Global;
use std::collections::BTreeSet;
use std::ops::{Deref, DerefMut};
use worker::Worker;

fn ensure_memory_trace_consistency<F: PrimeField>(
    memory_trace: &GKRMemoryOnlyWitnessTrace<F, impl std::alloc::Allocator + Clone, impl std::alloc::Allocator + Clone>,
    witness_trace: &GKRFullWitnessTrace<F, impl std::alloc::Allocator + Clone, impl std::alloc::Allocator + Clone>,
) {
    assert_eq!(
        memory_trace.column_major_trace.len(),
        witness_trace.column_major_memory_trace.len()
    );
    for (col, from_mem) in memory_trace.column_major_trace.iter().enumerate() {
        let from_wit = &witness_trace.column_major_memory_trace[col];
        assert_eq!(from_mem.len(), from_wit.len());
        for (row, (a, b)) in from_mem.iter().zip(from_wit.iter()).enumerate() {
            assert_eq!(*a, *b, "diverged for column {}, row {}", col, row);
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_test() {
    type CountersT = DelegationsAndFamiliesCounters;

    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    let worker = Worker::new_with_num_threads(8);
    // load binary

    // let binary = std::fs::read("../examples/basic_fibonacci/app.bin").unwrap();
    let binary = std::fs::read("../examples/hashed_fibonacci/app.bin").unwrap();
    // let binary = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.bin").unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section = std::fs::read("../examples/basic_fibonacci/app.text").unwrap();
    let text_section = std::fs::read("../examples/hashed_fibonacci/app.text").unwrap();
    // let text_section = std::fs::read("../riscv_transpiler/examples/keccak_f1600/app.text").unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // first run to capture minimal information
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text_section);

    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished); // check that we reached looping state (ie. end state for our vm)

    dbg!(state.counters);

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    let (num_trivial, _inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
        1,
        NUM_CYCLES_PER_CHUNK * NUM_INIT_AND_TEARDOWN_SETS,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    // let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
    //     .into_iter()
    //     .flatten()
    //     .collect();

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

    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);

    let permutation_argument_linearization_challenges: [E4; NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let external_challenges = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    // evaluate memory witness
    let preprocessing_data = process_binary_into_separate_tables_ext::<BF, true, Global>(
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

    println!("Will try to prove ADD/SUB/LUI/AUIPC/MOP circuit");

    let add_sub_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
    dbg!(num_calls);

    let mut state = snapshotter.initial_snapshot.state;

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
        buffers: &mut buffers[..],
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let (decoder_table_data, witness_gen_data) =
        &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: witness_gen_data,
        default_pc_value_in_padding: 4,
    };

    println!("Computing memory trace");
    let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );

    // {
    //     let memory_layout = &add_sub_circuit.memory_layout;
    //     let aux_layout_data = &add_sub_circuit.aux_layout_data;
    //     let context = ProverContext::new(&ProverContextConfig::default()).unwrap();
    //     let h_decoder_table = witness_gen_data
    //         .iter()
    //         .copied()
    //         .map(|d| d.into())
    //         .collect_vec();
    //     let mut d_decoder_table = context
    //         .alloc(h_decoder_table.len(), AllocationPlacement::BestFit)
    //         .unwrap();
    //     memory_copy(&mut d_decoder_table, &h_decoder_table).unwrap();
    //     let mut d_trace = context
    //         .alloc(buffer.len(), AllocationPlacement::BestFit)
    //         .unwrap();
    //     memory_copy(&mut d_trace, &buffer[..]).unwrap();
    //     let d_trace = UnrolledNonMemoryTraceDevice {
    //         tracing_data: d_trace,
    //     };
    //     let mut d_memory =
    //         DeviceAllocation::alloc(memory_layout.total_width * NUM_CYCLES_PER_CHUNK).unwrap();
    //     generate_memory_values_unrolled_non_memory(
    //         UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
    //         memory_layout,
    //         &d_decoder_table,
    //         &d_trace,
    //         &mut DeviceMatrixMut::new(&mut d_memory, NUM_CYCLES_PER_CHUNK),
    //         &CudaStream::DEFAULT,
    //     )
    //     .unwrap();
    //     let mut h_memory = vec![BF::ZERO; memory_layout.total_width * NUM_CYCLES_PER_CHUNK];
    //     memory_copy(&mut h_memory, &d_memory).unwrap();
    //     for row in 0..NUM_CYCLES_PER_CHUNK {
    //         let mut cpu_row = vec![];
    //         let mut gpu_row = vec![];
    //         for col in 0..memory_layout.total_width {
    //             let cpu_col = &_memory_trace.column_major_trace[col];
    //             let gpu_col = &h_memory[col * NUM_CYCLES_PER_CHUNK..][..NUM_CYCLES_PER_CHUNK];
    //             cpu_row.push(cpu_col[row]);
    //             gpu_row.push(gpu_col[row]);
    //         }
    //         assert_eq!(cpu_row, gpu_row, "row {} is not equal", row);
    //     }
    // }

    println!("Computing full trace");
    let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        add_sub_lui_auipc_mod::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &TableDriver::new(),
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

    // println!("Will check constraints satisfiability");
    // let is_satisfied = check_satisfied(&add_sub_circuit, &full_trace);
    // assert!(is_satisfied);

    println!("Preparing twiddles");
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    // let lde_precomputations =
    //     LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
    println!("Preparing setup");
    let setup = GKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &add_sub_circuit,
    );

    let setup_commitment = setup.commit(
        &twiddles,
        lde_factor,
        1,
        tree_cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    {
        let circuit_type = UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop;
        let memory_layout = &add_sub_circuit.memory_layout;
        let witness_layout = &add_sub_circuit.witness_layout;
        let aux_layout_data = &add_sub_circuit.aux_layout_data;
        let context = ProverContext::new(&ProverContextConfig::default()).unwrap();
        let h_decoder_table = witness_gen_data
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table = context
            .alloc(h_decoder_table.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut d_decoder_table, &h_decoder_table).unwrap();
        let mut d_trace = context
            .alloc(buffer.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut d_trace, &buffer[..]).unwrap();
        let d_trace = UnrolledNonMemoryTraceDevice {
            tracing_data: d_trace,
        };
        let mut d_memory =
            DeviceAllocation::alloc(memory_layout.total_width * NUM_CYCLES_PER_CHUNK).unwrap();
        let generic_lookups_count = {
            let count = witness_layout.generic_lookups.len();
            if add_sub_circuit.has_decoder_lookup {
                count + 1
            } else {
                count
            }
        };
        let mut d_generic_lookup_mapping = context
            .alloc(
                generic_lookups_count * NUM_CYCLES_PER_CHUNK,
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let (d_decoder_lookup_mapping_slice, d_generic_lookup_mapping_slice) =
            if add_sub_circuit.has_decoder_lookup {
                d_generic_lookup_mapping.split_at_mut(NUM_CYCLES_PER_CHUNK)
            } else {
                (
                    DeviceSlice::empty_mut(),
                    d_generic_lookup_mapping.deref_mut(),
                )
            };
        let mut trace_data = context
            .alloc(buffer.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut trace_data, &buffer[..]).unwrap();
        let d_trace = UnrolledNonMemoryTraceDevice {
            tracing_data: trace_data,
        };
        let h_setup = &setup.hypercube_evals;
        let mut d_setup = context
            .alloc(
                h_setup.len() * NUM_CYCLES_PER_CHUNK,
                AllocationPlacement::BestFit,
            )
            .unwrap();
        for (h, d) in h_setup.iter().zip(d_setup.chunks_mut(NUM_CYCLES_PER_CHUNK)) {
            memory_copy(d, &h[..]).unwrap();
        }
        let d_generic_lookup_tables = &d_setup[2 * NUM_CYCLES_PER_CHUNK..];
        let mut d_witness = context
            .alloc(
                witness_layout.total_width * NUM_CYCLES_PER_CHUNK,
                AllocationPlacement::BestFit,
            )
            .unwrap();

        generate_memory_and_witness_values_unrolled_non_memory(
            circuit_type,
            memory_layout,
            aux_layout_data,
            &d_decoder_table,
            &d_trace,
            &mut DeviceMatrixMut::new(&mut d_memory, NUM_CYCLES_PER_CHUNK),
            &mut DeviceMatrixMut::new(&mut d_witness, NUM_CYCLES_PER_CHUNK),
            d_decoder_lookup_mapping_slice,
            &CudaStream::DEFAULT,
        )
        .unwrap();
        generate_witness_values_unrolled_non_memory(
            circuit_type,
            &d_trace,
            &DeviceMatrix::new(d_generic_lookup_tables, NUM_CYCLES_PER_CHUNK),
            &DeviceMatrix::new(&d_memory, NUM_CYCLES_PER_CHUNK),
            &mut DeviceMatrixMut::new(&mut d_witness, NUM_CYCLES_PER_CHUNK),
            &mut DeviceMatrixMut::new(d_generic_lookup_mapping_slice, NUM_CYCLES_PER_CHUNK),
            &CudaStream::DEFAULT,
        )
        .unwrap();
        let range = witness_layout
            .multiplicities_columns_for_generic_lookup
            .clone();
        let generic_lookup_multiplicities =
            &mut d_witness[range.start * NUM_CYCLES_PER_CHUNK..range.end * NUM_CYCLES_PER_CHUNK];
        generate_generic_lookup_multiplicities(
            &mut DeviceMatrixMut::new(&mut d_generic_lookup_mapping, NUM_CYCLES_PER_CHUNK),
            &mut DeviceMatrixMut::new(generic_lookup_multiplicities, NUM_CYCLES_PER_CHUNK),
            &context,
        )
        .unwrap();
        generate_range_check_multiplicities(
            &add_sub_circuit,
            &mut DeviceMatrixMut::new(&mut d_memory, NUM_CYCLES_PER_CHUNK),
            &mut DeviceMatrixMut::new(&mut d_witness, NUM_CYCLES_PER_CHUNK),
            &context,
        )
        .unwrap();
        let mut h_memory = vec![BF::ZERO; memory_layout.total_width * NUM_CYCLES_PER_CHUNK];
        memory_copy(&mut h_memory, &d_memory).unwrap();
        for row in 0..NUM_CYCLES_PER_CHUNK {
            let mut cpu_row = vec![];
            let mut gpu_row = vec![];
            for col in 0..memory_layout.total_width {
                let cpu_col = &full_trace.column_major_memory_trace[col];
                let gpu_col = &h_memory[col * NUM_CYCLES_PER_CHUNK..][..NUM_CYCLES_PER_CHUNK];
                cpu_row.push(cpu_col[row]);
                gpu_row.push(gpu_col[row]);
            }
            assert_eq!(cpu_row, gpu_row, "row {} is not equal", row);
        }
        let mut h_witness = vec![BF::ZERO; witness_layout.total_width * NUM_CYCLES_PER_CHUNK];
        memory_copy(&mut h_witness, &d_witness).unwrap();
        for row in 0..NUM_CYCLES_PER_CHUNK {
            let mut cpu_row = vec![];
            let mut gpu_row = vec![];
            for col in 0..witness_layout.total_width {
                let cpu_col = &full_trace.column_major_witness_trace[col];
                let gpu_col = &h_witness[col * NUM_CYCLES_PER_CHUNK..][..NUM_CYCLES_PER_CHUNK];
                cpu_row.push(cpu_col[row]);
                gpu_row.push(gpu_col[row]);
            }
            assert_eq!(cpu_row, gpu_row, "row {} is not equal", row);
        }
    }

    println!("Trying to prove");

    let now = std::time::Instant::now();
    let _proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        &add_sub_circuit,
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
}

#[allow(unused_imports)]
mod add_sub_lui_auipc_mod {
    use crate::field::BF;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::unrolled::NonMemoryCircuitOracle;
    use prover::witness_proxy::WitnessProxy;

    include!("../../prover/add_sub_lui_auipc_mop_preprocessed_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}
