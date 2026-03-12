use super::gkr::{
    setup::{GpuGKRSetupHost, GpuGKRSetupTransfer},
    GpuGKRStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::set_by_ref;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::UnrolledNonMemoryCircuitType;
use crate::primitives::context::ProverContext;
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode};
use crate::witness::memory_unrolled::generate_memory_and_witness_values_unrolled_non_memory;
use crate::witness::multiplicities::{
    generate_generic_lookup_multiplicities, generate_range_check_multiplicities,
};
use crate::witness::trace_unrolled::UnrolledNonMemoryTraceDevice;
use crate::witness::witness_unrolled::generate_witness_values_unrolled_non_memory;
use cs::definitions::*;
use cs::gkr_compiler::OutputType;
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
use field::{Field, FieldExtension, PrimeField};
use itertools::Itertools;
use prover::definitions::Transcript;
use prover::gkr::prover::dimension_reduction::{self, forward::DimensionReducingInputOutput};
use prover::gkr::prover::forward_loop;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::prover::stages::stage1;
use prover::gkr::prover::sumcheck_loop;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::{GKRExternalChallenges, GKRProof, WhirSchedule};
use prover::gkr::sumcheck::access_and_fold::GKRStorage;
use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
use prover::gkr::whir::whir_fold;
use prover::gkr::witness_gen::family_circuits::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
use prover::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
};
use prover::prover_stages::flatten_merkle_caps_iter_into;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::unrolled::NonMemoryCircuitOracle;
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
use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::path::PathBuf;
use std::sync::Arc;
use worker::Worker;

fn test_artifact_path(relative_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(relative_path)
}

fn ensure_memory_trace_consistency<F: PrimeField>(
    memory_trace: &GKRMemoryOnlyWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
    witness_trace: &GKRFullWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
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

fn evaluate_ext_poly_with_eq<E: Field>(values: &[E], eq: &[E]) -> E {
    assert_eq!(values.len(), eq.len());
    let mut result = E::ZERO;
    for (value, eq_value) in values.iter().zip(eq.iter()) {
        let mut term = *value;
        term.mul_assign(eq_value);
        result.add_assign(&term);
    }
    result
}

fn evaluate_base_poly_with_eq<F: PrimeField, E: FieldExtension<F> + Field>(
    values: &[F],
    eq: &[E],
) -> E {
    assert_eq!(values.len(), eq.len());
    let mut result = E::ZERO;
    for (value, eq_value) in values.iter().zip(eq.iter()) {
        let mut term = *eq_value;
        term.mul_assign_by_base(value);
        result.add_assign(&term);
    }
    result
}

fn compute_initial_sumcheck_claims_for_test<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    eval_point: &[E],
    output_layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    worker: &Worker,
) -> [E; 8] {
    let eq_precomputed = make_eq_poly_in_full::<E>(eval_point, worker);
    let eq = eq_precomputed.last().unwrap();

    let mut evals = vec![];
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        let addresses = &output_layer[&key];
        for address in addresses.output.iter() {
            let poly = gkr_storage.get_ext_poly(*address);
            evals.push(evaluate_ext_poly_with_eq(poly, &eq[..]));
        }
    }

    evals.try_into().unwrap()
}

fn stage1_caps_from_tree<T: ColumnMajorMerkleTreeConstructor<BF>>(
    tree: &T,
    subcap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    tree.get_cap()
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
}

fn materialize_trace_holder_from_columns(
    values: &DeviceSlice<BF>,
    columns_count: usize,
    trace_len: usize,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> TraceHolder<BF> {
    let mut trace_holder = TraceHolder::<BF>::new(
        trace_len.trailing_zeros(),
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        context,
    )
    .unwrap();
    trace_holder
        .materialize_and_commit_from_hypercube_evals(values, context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    trace_holder
}

fn copy_base_poly_from_gpu_storage<E: Field>(
    storage: &GpuGKRStorage<BF, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<BF> {
    let poly = storage.get_base_layer(address);
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut host = vec![BF::ZERO; poly.len()];
    memory_copy(&mut host, &tmp).unwrap();
    host
}

fn assert_storage_base_columns_match_cpu_trace<Column: AsRef<[BF]>, E: Field>(
    storage: &GpuGKRStorage<BF, E>,
    make_address: impl Fn(usize) -> GKRAddress,
    cpu_columns: &[Column],
    context: &ProverContext,
) {
    for (column_idx, cpu_column) in cpu_columns.iter().enumerate() {
        let address = make_address(column_idx);
        let gpu_column = copy_base_poly_from_gpu_storage(storage, address, context);
        assert_eq!(
            gpu_column,
            cpu_column.as_ref(),
            "storage column {:?} diverged",
            address,
        );
    }
}

fn assert_flat_columns_match_cpu_trace<Column: AsRef<[BF]>>(
    gpu_flat_columns: &[BF],
    cpu_columns: &[Column],
    trace_len: usize,
) {
    assert_eq!(gpu_flat_columns.len(), cpu_columns.len() * trace_len);
    for (column_idx, cpu_column) in cpu_columns.iter().enumerate() {
        let gpu_column = &gpu_flat_columns[column_idx * trace_len..(column_idx + 1) * trace_len];
        assert_eq!(
            gpu_column,
            cpu_column.as_ref(),
            "column {} diverged",
            column_idx
        );
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
    let worker = Worker::new_with_num_threads(8);
    // load binary

    // let binary = std::fs::read(test_artifact_path("examples/basic_fibonacci/app.bin")).unwrap();
    let binary = std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.bin")).unwrap();
    // let binary = std::fs::read(test_artifact_path("riscv_transpiler/examples/keccak_f1600/app.bin")).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section =
    //     std::fs::read(test_artifact_path("examples/basic_fibonacci/app.text")).unwrap();
    let text_section =
        std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.text")).unwrap();
    // let text_section =
    //     std::fs::read(test_artifact_path("riscv_transpiler/examples/keccak_f1600/app.text"))
    //         .unwrap();
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

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

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

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

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

    let add_sub_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

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

    let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );

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

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    let base_lde_factor = whir_schedule.base_lde_factor;
    let tree_cap_size = whir_schedule.cap_size;
    let setup = GKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &add_sub_circuit,
    );
    let whir_first_fold_step_log2 = 1usize;

    let setup_commitment = setup.commit(
        &twiddles,
        base_lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let log_lde_factor = base_lde_factor.trailing_zeros();
    let log_rows_per_leaf = whir_first_fold_step_log2 as u32;
    let log_tree_cap_size = tree_cap_size.trailing_zeros();
    let subcap_size = tree_cap_size / base_lde_factor;
    let context = make_test_context(20 * 1024, 1024);
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap(),
    );
    let mut gpu_setup_transfer =
        GpuGKRSetupTransfer::new(Arc::clone(&gpu_setup_host), &context).unwrap();
    gpu_setup_transfer.schedule_transfer(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let (d_memory, d_witness) = {
        let circuit_type = UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop;
        let memory_layout = &add_sub_circuit.memory_layout;
        let witness_layout = &add_sub_circuit.witness_layout;
        let aux_layout_data = &add_sub_circuit.aux_layout_data;
        let h_decoder_table = witness_gen_data
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table = context
            .alloc(h_decoder_table.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut d_decoder_table, &h_decoder_table).unwrap();
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
        let d_setup = gpu_setup_transfer.trace_holder.get_hypercube_evals();
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
        assert_flat_columns_match_cpu_trace(
            &h_memory,
            &full_trace.column_major_memory_trace,
            NUM_CYCLES_PER_CHUNK,
        );
        let mut h_witness = vec![BF::ZERO; witness_layout.total_width * NUM_CYCLES_PER_CHUNK];
        memory_copy(&mut h_witness, &d_witness).unwrap();
        assert_flat_columns_match_cpu_trace(
            &h_witness,
            &full_trace.column_major_witness_trace,
            NUM_CYCLES_PER_CHUNK,
        );
        (d_memory, d_witness)
    };

    let now = std::time::Instant::now();
    assert_eq!(add_sub_circuit.trace_len, trace_len);
    assert_eq!(full_trace.column_major_memory_trace[0].len(), trace_len);

    let (mem_oracle, wit_oracle) = stage1::stage1::<BF, DefaultTreeConstructor>(
        &full_trace,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    let trace_holder_caps = gpu_setup_transfer.trace_holder.get_tree_caps();
    let setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    assert_eq!(trace_holder_caps, setup_caps);

    let memory_trace_holder = materialize_trace_holder_from_columns(
        &d_memory,
        add_sub_circuit.memory_layout.total_width,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );
    let memory_caps = stage1_caps_from_tree(&mem_oracle.tree, subcap_size);
    assert_eq!(memory_trace_holder.get_tree_caps(), memory_caps);

    let witness_trace_holder = materialize_trace_holder_from_columns(
        &d_witness,
        add_sub_circuit.witness_layout.total_width,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );
    let witness_caps = stage1_caps_from_tree(&wit_oracle.tree, subcap_size);
    assert_eq!(witness_trace_holder.get_tree_caps(), witness_caps);

    let gpu_gkr_storage =
        gpu_setup_transfer.bootstrap_storage::<E4>(&memory_trace_holder, &witness_trace_holder);
    assert_eq!(gpu_gkr_storage.layers.len(), 1);
    assert!(gpu_gkr_storage.layers[0].extension_field_inputs.is_empty());
    let setup_columns = setup
        .hypercube_evals
        .iter()
        .map(|column| column.as_ref().as_ref())
        .collect_vec();
    assert_storage_base_columns_match_cpu_trace(
        &gpu_gkr_storage,
        GKRAddress::Setup,
        &setup_columns,
        &context,
    );
    assert_storage_base_columns_match_cpu_trace(
        &gpu_gkr_storage,
        GKRAddress::BaseLayerMemory,
        &full_trace.column_major_memory_trace,
        &context,
    );
    assert_storage_base_columns_match_cpu_trace(
        &gpu_gkr_storage,
        GKRAddress::BaseLayerWitness,
        &full_trace.column_major_witness_trace,
        &context,
    );

    let mut transcript_input = vec![];
    external_challenges.flatten_into_buffer(&mut transcript_input);
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &setup_commitment.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &mem_oracle.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &wit_oracle.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();

    let mut lookup_challenges = unsafe { context.alloc_host_uninit_slice(2) };
    unsafe {
        lookup_challenges
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&[lookup_alpha, lookup_additive_part]);
    }
    let mut callbacks = Callbacks::new();
    let mut gpu_lookup_runtime_data = gpu_setup_transfer
        .prepare_lookup_runtime_data(&add_sub_circuit, &context)
        .unwrap();
    gpu_setup_transfer
        .schedule_lookup_runtime_data(
            &mut gpu_lookup_runtime_data,
            lookup_challenges.get_accessor(),
            &mut callbacks,
            &context,
        )
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    let (
        preprocessed_range_check_16,
        preprocessed_timestamp_range_checks,
        preprocessed_generic_lookup,
    ) = setup.preprocess_lookups(
        &add_sub_circuit,
        lookup_alpha,
        lookup_additive_part,
        trace_len,
        &mut gkr_storage,
        &worker,
    );

    let mut gpu_range = vec![E4::ZERO; gpu_lookup_runtime_data.range_check_16.len()];
    memory_copy(&mut gpu_range, &gpu_lookup_runtime_data.range_check_16).unwrap();
    assert_eq!(gpu_range, preprocessed_range_check_16.as_ref());

    let mut gpu_timestamp = vec![E4::ZERO; gpu_lookup_runtime_data.timestamp_range_check.len()];
    memory_copy(
        &mut gpu_timestamp,
        &gpu_lookup_runtime_data.timestamp_range_check,
    )
    .unwrap();
    assert_eq!(gpu_timestamp, preprocessed_timestamp_range_checks.as_ref());

    let mut gpu_generic = vec![E4::ZERO; gpu_lookup_runtime_data.generic_lookup.len()];
    memory_copy(&mut gpu_generic, &gpu_lookup_runtime_data.generic_lookup).unwrap();
    assert_eq!(gpu_generic, preprocessed_generic_lookup.as_ref());

    let gpu_vectorized_lookup_setup = gpu_lookup_runtime_data.vectorized_lookup_setup_poly();
    let mut gpu_vectorized_host = vec![E4::ZERO; gpu_vectorized_lookup_setup.len()];
    memory_copy(&mut gpu_vectorized_host, gpu_vectorized_lookup_setup).unwrap();
    assert_eq!(
        &gpu_vectorized_host[..preprocessed_generic_lookup.len()],
        preprocessed_generic_lookup.as_ref()
    );
    assert!(gpu_vectorized_host[preprocessed_generic_lookup.len()..]
        .iter()
        .all(|value| *value == lookup_additive_part));

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &add_sub_circuit,
            &external_challenges,
            &mut witness_eval_data,
            trace_len,
            &preprocessed_generic_lookup,
            lookup_additive_part,
            constraints_batch_challenge,
            &worker,
        );
    }

    let final_trace_size_log_2 = 4;
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            &add_sub_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            &worker,
        );

    let mut final_explicit_evaluations = BTreeMap::new();
    let mut evals_flattened = vec![];
    for (k, v) in dimension_reducing_inputs[&initial_layer_for_sumcheck].iter() {
        match *k {
            OutputType::PermutationProduct => {
                let mut final_evals: [Vec<E4>; 2] = std::array::from_fn(|_| Vec::new());
                for (i, addr) in v.output.iter().enumerate() {
                    let poly = gkr_storage.get_ext_poly(*addr);
                    assert_eq!(poly.len(), 1 << final_trace_size_log_2);
                    evals_flattened.extend_from_slice(poly);
                    final_evals[i] = poly.to_vec();
                }
                final_explicit_evaluations.insert(*k, final_evals);
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let [num, den] = v.output.clone().try_into().unwrap();
                let num = gkr_storage.get_ext_poly(num);
                evals_flattened.extend_from_slice(num);
                let den = gkr_storage.get_ext_poly(den);
                evals_flattened.extend_from_slice(den);
                final_explicit_evaluations.insert(*k, [num.to_vec(), den.to_vec()]);
            }
        }
    }
    commit_field_els::<BF, E4>(&mut seed, &evals_flattened);

    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges = draw_random_field_els::<BF, E4>(&mut seed, num_challenges);
    let batching_challenge = challenges.pop().unwrap();

    let evaluation_point = challenges;
    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        compute_initial_sumcheck_claims_for_test(
            &gkr_storage,
            &evaluation_point,
            &dimension_reducing_inputs[&initial_layer_for_sumcheck],
            &worker,
        );

    let output_map = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    let mut top_layer_claims: BTreeMap<GKRAddress, E4> = BTreeMap::new();
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits].output[0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits].output[1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    let mut claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E4>> = BTreeMap::new();
    let mut points_for_claims_at_layer = BTreeMap::new();
    claims_for_layers.insert(initial_layer_for_sumcheck + 1, top_layer_claims);
    points_for_claims_at_layer.insert(initial_layer_for_sumcheck + 1, evaluation_point);

    let mut sumcheck_intermediate_values = BTreeMap::new();
    let mut sumcheck_batching_challenge = batching_challenge;
    let mut reduced_trace_size_log_2 = final_trace_size_log_2;
    for (layer_idx, layer) in dimension_reducing_inputs.into_iter().rev() {
        let proof = sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer(
            layer_idx,
            &layer,
            &mut points_for_claims_at_layer,
            &mut claims_for_layers,
            &mut gkr_storage,
            &mut sumcheck_batching_challenge,
            &mut seed,
            1 << reduced_trace_size_log_2,
            &worker,
        );
        sumcheck_intermediate_values.insert(layer_idx, proof);
        reduced_trace_size_log_2 += 1;
    }

    assert_eq!(1 << reduced_trace_size_log_2, trace_len);

    for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate().rev() {
        let proof = sumcheck_loop::evaluate_sumcheck_for_layer(
            layer_idx,
            layer,
            &mut points_for_claims_at_layer,
            &mut claims_for_layers,
            &mut gkr_storage,
            &mut sumcheck_batching_challenge,
            &add_sub_circuit,
            trace_len,
            lookup_additive_part,
            constraints_batch_challenge,
            &mut seed,
            &worker,
        );
        sumcheck_intermediate_values.insert(layer_idx, proof);
    }

    let base_layer_z = points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point");
    let eq_precomputed = make_eq_poly_in_full(base_layer_z, &worker);
    let eq_at_z = eq_precomputed.last().unwrap();

    let layer_desc = &add_sub_circuit.layers[0];
    let base_layer_claims = claims_for_layers.entry(0).or_insert_with(BTreeMap::new);
    for (cached_addr, relation) in layer_desc.cached_relations.iter() {
        debug_assert!(
            base_layer_claims.contains_key(cached_addr),
            "Missing claim for cached address {:?}",
            cached_addr
        );

        for dep in relation.dependencies() {
            if base_layer_claims.contains_key(&dep) {
                continue;
            }
            match dep {
                GKRAddress::BaseLayerWitness(_)
                | GKRAddress::BaseLayerMemory(_)
                | GKRAddress::Setup(_) => {
                    let values = gkr_storage.get_base_layer(dep);
                    let evaluation = evaluate_base_poly_with_eq::<BF, E4>(values, &eq_at_z[..]);
                    base_layer_claims.insert(dep, evaluation);
                }
                _ => {
                    panic!(
                        "Unexpected dependency address {:?} for cached relation {:?}",
                        dep, cached_addr
                    );
                }
            }
        }
    }

    drop(preprocessed_range_check_16);
    drop(preprocessed_timestamp_range_checks);
    drop(preprocessed_generic_lookup);

    let mut mem_polys_claims = Vec::with_capacity(add_sub_circuit.memory_layout.total_width);
    for i in 0..add_sub_circuit.memory_layout.total_width {
        let key = GKRAddress::BaseLayerMemory(i);
        let value = claims_for_layers[&0]
            .get(&key)
            .copied()
            .unwrap_or_else(|| panic!("Missing claim for {:?}", key));
        mem_polys_claims.push(value);
    }

    let mut wit_polys_claims = Vec::with_capacity(add_sub_circuit.witness_layout.total_width);
    for i in 0..add_sub_circuit.witness_layout.total_width {
        let key = GKRAddress::BaseLayerWitness(i);
        let value = claims_for_layers[&0]
            .get(&key)
            .copied()
            .unwrap_or_else(|| panic!("Missing claim for {:?}", key));
        wit_polys_claims.push(value);
    }

    let mut setup_polys_claims = Vec::with_capacity(setup.hypercube_evals.len());
    for i in 0..setup.hypercube_evals.len() {
        let key = GKRAddress::Setup(i);
        let value = claims_for_layers[&0]
            .get(&key)
            .copied()
            .unwrap_or_else(|| panic!("Missing claim for {:?}", key));
        let evaluation =
            evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
        assert_eq!(evaluation, value, "diverged for {:?}", key);
        setup_polys_claims.push(value);
    }

    drop(gkr_storage);

    let whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
    let whir_schedule = whir_schedule.clone();
    let whir_proof = whir_fold(
        mem_oracle,
        mem_polys_claims,
        wit_oracle,
        wit_polys_claims,
        &setup_commitment,
        setup_polys_claims,
        base_layer_z.clone(),
        whir_schedule.base_lde_factor,
        whir_batching_challenge,
        whir_schedule.whir_steps_schedule,
        whir_schedule.whir_queries_schedule,
        whir_schedule.whir_steps_lde_factors,
        whir_schedule.whir_pow_schedule,
        &twiddles,
        seed,
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    let [read_set_computed, write_set_computed] = final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("must be present")
        .clone()
        .map(|els| {
            let mut result = E4::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
    let mut grand_product_accumulator_computed = read_set_computed;
    grand_product_accumulator_computed
        .mul_assign(&write_set_computed.inverse().expect("must not be zero"));

    let _proof = GKRProof::<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        external_challenges,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        whir_proof,
        grand_product_accumulator_computed,
    };
    let _elapsed = now.elapsed();
}

#[allow(unused_imports)]
mod add_sub_lui_auipc_mod {
    use crate::primitives::field::BF;
    use cs::cs::placeholder::Placeholder;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::cs::witness_placer::WitnessTypeSet;
    use cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::unrolled::NonMemoryCircuitOracle;
    use prover::witness_proxy::WitnessProxy;

    include!("../../../prover/add_sub_lui_auipc_mop_preprocessed_generated_gkr.rs");

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
