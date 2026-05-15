use super::*;

#[test]
#[ignore]
fn test_commit_memory_matches_cpu() {
    let compiled_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        24,
    );
    assert_non_memory_commit_memory_matches_cpu_for_test::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
        "examples/basic_fibonacci/app.bin",
        "examples/basic_fibonacci/app.text",
        &[],
        4,
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        compiled_circuit,
    );
}

#[test]
#[ignore]
fn test_jump_branch_slt_commit_memory_matches_cpu() {
    let compiled_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| jump_branch_slt_table_addition_fn(cs),
        &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        24,
    );
    assert_non_memory_commit_memory_matches_cpu_for_test::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        "examples/hashed_fibonacci/app.bin",
        "examples/hashed_fibonacci/app.text",
        &[15, 1],
        0,
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        compiled_circuit,
    );
}

#[test]
#[ignore]
fn test_shift_binop_commit_memory_matches_cpu() {
    let compiled_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| shift_binop_table_addition_fn(cs),
        &|cs| shift_binop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        24,
    );
    assert_non_memory_commit_memory_matches_cpu_for_test::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        "examples/hashed_fibonacci/app.bin",
        "examples/hashed_fibonacci/app.text",
        &[15, 1],
        4,
        UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        compiled_circuit,
    );
}

#[test]
#[ignore]
fn test_load_store_word_only_commit_memory_matches_cpu() {
    let binary = read_test_words("examples/hashed_fibonacci/app.bin");
    let compiled_circuit = compile_mem_word_only_circuit_for_test(&binary);
    assert_memory_commit_memory_matches_cpu_for_test::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(
        "examples/hashed_fibonacci/app.bin",
        "examples/hashed_fibonacci/app.text",
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
        compiled_circuit,
    );
}

#[test]
#[ignore]
fn test_load_store_subword_only_commit_memory_matches_cpu() {
    let binary = read_test_words("riscv_transpiler/examples/keccak_f1600/app.bin");
    let compiled_circuit = compile_mem_subword_only_circuit_for_test(&binary);
    assert_memory_commit_memory_matches_cpu_for_test::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(
        "riscv_transpiler/examples/keccak_f1600/app.bin",
        "riscv_transpiler/examples/keccak_f1600/app.text",
        &[],
        UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        compiled_circuit,
    );
}

#[test]
#[ignore]
fn test_bigint_delegation_commit_memory_matches_cpu() {
    let compiled_circuit = deserialize_json_for_test(
        "cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json",
    );
    assert_bigint_delegation_commit_memory_matches_cpu(compiled_circuit, false);
}

#[test]
#[ignore]
fn test_blake2_delegation_commit_memory_matches_cpu() {
    let compiled_circuit = deserialize_json_for_test(
        "cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json",
    );
    assert_blake2_delegation_commit_memory_matches_cpu(compiled_circuit, false);
}

#[test]
#[ignore]
fn test_keccak_special5_delegation_commit_memory_matches_cpu() {
    let compiled_circuit =
        deserialize_json_for_test("cs/compiled_circuits/keccak_special5_layout_gkr.json");
    assert_keccak_delegation_commit_memory_matches_cpu(compiled_circuit);
}

#[test]
#[ignore]
fn test_blake2_delegation_zero_call_commit_memory_matches_cpu() {
    let compiled_circuit = deserialize_json_for_test(
        "cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json",
    );
    assert_blake2_delegation_commit_memory_matches_cpu(compiled_circuit, true);
}

fn assert_non_memory_commit_memory_matches_cpu_for_test<const FAMILY_IDX: u8>(
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: &[u32],
    default_pc_value_in_padding: u32,
    circuit_type: UnrolledNonMemoryCircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
) {
    use crate::prover::trace::memory::commit_memory;
    use prover::gkr::prover::stages::stage1::commit_trace_part;
    use prover::gkr::witness_gen::family_circuits::evaluate_gkr_memory_witness_for_executor_family;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    const DEVICE_ALLOCATOR_ARENA_BYTES: usize = 64usize << 30;
    const HOST_POOL_SIZE_MB: usize = 1024;
    const DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

    let binary = std::fs::read(test_artifact_path(binary_path)).unwrap();
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let text_section = std::fs::read(test_artifact_path(text_path)).unwrap();
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_reads.to_vec());
    let is_finished = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    assert!(
        num_calls > 0,
        "selected workload must exercise family {FAMILY_IDX}",
    );
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<FAMILY_IDX> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
        &mut replay_state,
        &mut replay_ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    drop(replay_ram);

    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
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
    let decoder_table_data = preprocessing_data
        .remove(&FAMILY_IDX)
        .expect("must have data");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let worker = Worker::new_with_num_threads(8);
    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
        default_pc_value_in_padding,
    };
    let trace_len = compiled_circuit.trace_len;
    let cpu_memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &compiled_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );

    let twiddles: fft::Twiddles<BF, Global> = fft::Twiddles::new(trace_len, &worker);
    let non_memory_circuit_type =
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type));
    let prover_config = non_memory_circuit_type
        .prover_config(SecurityLevel::Sec80)
        .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let mem_inputs: Vec<_> = cpu_memory_trace
        .column_major_trace
        .iter()
        .map(|col| &col[..])
        .collect();
    let cpu_mem_oracle = commit_trace_part::<BF, DefaultTreeConstructor>(
        &mem_inputs,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let mut cpu_transcript = vec![];
    let cpu_cap: MerkleTreeCapVarLength =
        ColumnMajorMerkleTreeConstructor::<BF>::get_cap(&cpu_mem_oracle.tree);
    flatten_merkle_caps_iter_into(Some(cpu_cap).into_iter(), &mut cpu_transcript);
    let device_block_size = 1usize << DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let max_device_allocation_blocks_count = DEVICE_ALLOCATOR_ARENA_BYTES / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
    );

    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect_vec();
    let d_decoder_table = if compiled_circuit.has_decoder_lookup {
        Some(upload_slice_to_device_for_test(&h_decoder_table, &context))
    } else {
        None
    };
    let trace_data = upload_slice_to_device_for_test(&buffer, &context);
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(
        UnrolledNonMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));

    let job = commit_memory(
        non_memory_circuit_type,
        &compiled_circuit,
        if compiled_circuit.has_decoder_lookup {
            Some(d_decoder_table.as_ref().unwrap())
        } else {
            None
        },
        &gpu_trace,
        &prover_config,
        &context,
    )
    .unwrap();

    let (gpu_tree_caps, elapsed_ms) = job.finish().unwrap();
    eprintln!("GPU memory commitment ready in {elapsed_ms:.1}ms");

    let mut gpu_transcript = vec![];
    flatten_merkle_caps_iter_into(gpu_tree_caps.into_iter(), &mut gpu_transcript);

    assert_eq!(
        cpu_transcript, gpu_transcript,
        "GPU memory tree caps must match CPU"
    );
    eprintln!("Memory commitment tree caps match!");
}

fn assert_memory_commit_memory_matches_cpu_for_test<const FAMILY_IDX: u8>(
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: &[u32],
    circuit_type: UnrolledMemoryCircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
) {
    use crate::prover::trace::memory::commit_memory;
    use prover::gkr::prover::stages::stage1::commit_trace_part;
    use prover::gkr::witness_gen::family_circuits::evaluate_gkr_memory_witness_for_executor_family;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    const DEVICE_ALLOCATOR_ARENA_BYTES: usize = 64usize << 30;
    const HOST_POOL_SIZE_MB: usize = 1024;
    const DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

    let binary = std::fs::read(test_artifact_path(binary_path)).unwrap();
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let text_section = std::fs::read(test_artifact_path(text_path)).unwrap();
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_reads.to_vec());
    let is_finished = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    assert!(
        num_calls > 0,
        "selected workload must exercise family {FAMILY_IDX}",
    );
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = MemDestinationHolder::<FAMILY_IDX> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
        &mut replay_state,
        &mut replay_ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    drop(replay_ram);

    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
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
    let decoder_table_data = preprocessing_data
        .remove(&FAMILY_IDX)
        .expect("must have data");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let worker = Worker::new_with_num_threads(8);
    let oracle = MemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
    };
    let trace_len = compiled_circuit.trace_len;
    let cpu_memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &compiled_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );

    let twiddles: fft::Twiddles<BF, Global> = fft::Twiddles::new(trace_len, &worker);
    let memory_circuit_type_value =
        CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type));
    let prover_config = memory_circuit_type_value
        .prover_config(SecurityLevel::Sec80)
        .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let mem_inputs: Vec<_> = cpu_memory_trace
        .column_major_trace
        .iter()
        .map(|col| &col[..])
        .collect();
    let cpu_mem_oracle = commit_trace_part::<BF, DefaultTreeConstructor>(
        &mem_inputs,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let mut cpu_transcript = vec![];
    let cpu_cap: MerkleTreeCapVarLength =
        ColumnMajorMerkleTreeConstructor::<BF>::get_cap(&cpu_mem_oracle.tree);
    flatten_merkle_caps_iter_into(Some(cpu_cap).into_iter(), &mut cpu_transcript);
    let device_block_size = 1usize << DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let max_device_allocation_blocks_count = DEVICE_ALLOCATOR_ARENA_BYTES / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
    );

    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect_vec();
    let d_decoder_table = if compiled_circuit.has_decoder_lookup {
        Some(upload_slice_to_device_for_test(&h_decoder_table, &context))
    } else {
        None
    };
    let trace_data = upload_slice_to_device_for_test(&buffer, &context);
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(
        UnrolledMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));

    let job = commit_memory(
        memory_circuit_type_value,
        &compiled_circuit,
        if compiled_circuit.has_decoder_lookup {
            Some(d_decoder_table.as_ref().unwrap())
        } else {
            None
        },
        &gpu_trace,
        &prover_config,
        &context,
    )
    .unwrap();

    let (gpu_tree_caps, elapsed_ms) = job.finish().unwrap();
    eprintln!("GPU memory commitment ready in {elapsed_ms:.1}ms");

    let mut gpu_transcript = vec![];
    flatten_merkle_caps_iter_into(gpu_tree_caps.into_iter(), &mut gpu_transcript);

    assert_eq!(
        cpu_transcript, gpu_transcript,
        "GPU memory tree caps must match CPU"
    );
    eprintln!("Memory commitment tree caps match!");
}

fn assert_delegation_commit_memory_matches_cpu<W, O, F>(
    label: &str,
    circuit_type: DelegationCircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    buffer: &[W],
    oracle: &O,
    build_gpu_trace: F,
) where
    W: Copy,
    O: cs::oracle::Oracle<BF>,
    F: FnOnce(crate::primitives::context::DeviceAllocation<W>) -> TracingDataDevice,
{
    const DEVICE_ALLOCATOR_ARENA_BYTES: usize = 64usize << 30;
    const HOST_POOL_SIZE_MB: usize = 1024;
    const DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

    let worker = Worker::new_with_num_threads(8);
    let trace_len = compiled_circuit.trace_len;
    let cpu_memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
        &compiled_circuit,
        circuit_type.get_domain_size(),
        oracle,
        &worker,
        Global,
        Global,
    );

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let prover_config = delegation_prover_config(circuit_type);
    let whir_schedule = prover_config.whir_schedule.clone();
    let mem_inputs: Vec<_> = cpu_memory_trace
        .column_major_trace
        .iter()
        .map(|col| &col[..])
        .collect();
    let cpu_mem_oracle = commit_trace_part::<BF, DefaultTreeConstructor>(
        &mem_inputs,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let mut cpu_transcript = vec![];
    let cpu_cap: MerkleTreeCapVarLength =
        ColumnMajorMerkleTreeConstructor::<BF>::get_cap(&cpu_mem_oracle.tree);
    flatten_merkle_caps_iter_into(Some(cpu_cap).into_iter(), &mut cpu_transcript);

    let device_block_size = 1usize << DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let max_device_allocation_blocks_count = DEVICE_ALLOCATOR_ARENA_BYTES / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
    );
    let trace_data = upload_slice_to_device_for_test(buffer, &context);
    let gpu_trace = build_gpu_trace(trace_data);

    let job = commit_memory(
        CircuitType::Delegation(circuit_type),
        &compiled_circuit,
        None,
        &gpu_trace,
        &prover_config,
        &context,
    )
    .unwrap();

    let (gpu_tree_caps, elapsed_ms) = job.finish().unwrap();
    eprintln!("{label}: GPU memory commitment ready in {elapsed_ms:.1}ms");

    let mut gpu_transcript = vec![];
    flatten_merkle_caps_iter_into(gpu_tree_caps.into_iter(), &mut gpu_transcript);
    assert_eq!(
        cpu_transcript, gpu_transcript,
        "{label}: GPU memory tree caps must match CPU"
    );
}
fn assert_bigint_delegation_commit_memory_matches_cpu(
    compiled_circuit: GKRCircuitArtifact<BF>,
    zero_call: bool,
) {
    let buffer = replay_delegation_trace_buffer(
        zero_call,
        |counters| counters.bigint_calls,
        BigintDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = vec![buffer];
            let mut tracer = BigintDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );

    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    assert_delegation_commit_memory_matches_cpu(
        "bigint_with_control",
        DelegationCircuitType::BigIntWithControl,
        compiled_circuit,
        &buffer,
        &oracle,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::BigIntWithControl(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}

fn assert_blake2_delegation_commit_memory_matches_cpu(
    compiled_circuit: GKRCircuitArtifact<BF>,
    zero_call: bool,
) {
    let buffer = replay_delegation_trace_buffer(
        zero_call,
        |counters| counters.blake_calls,
        Blake2sRoundFunctionDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = vec![buffer];
            let mut tracer = BlakeDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );

    let oracle = Blake2sDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    assert_delegation_commit_memory_matches_cpu(
        "blake2_with_compression",
        DelegationCircuitType::Blake2WithCompression,
        compiled_circuit,
        &buffer,
        &oracle,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2WithCompression(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}

fn assert_keccak_delegation_commit_memory_matches_cpu(compiled_circuit: GKRCircuitArtifact<BF>) {
    let buffer = replay_delegation_trace_buffer(
        false,
        |counters| counters.keccak_calls,
        KeccakSpecial5DelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = vec![buffer];
            let mut tracer = KeccakDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );
    let num_calls = buffer.len();
    assert!(
        num_calls > 0,
        "keccak_f1600 must exercise keccak delegation"
    );
    assert!(
        buffer
            .iter()
            .any(|cycle| cycle.variables_offsets.iter().any(|&value| value != 0)),
        "keccak fixture must exercise variable-offset indirect accesses",
    );

    let oracle = KeccakDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    assert_delegation_commit_memory_matches_cpu(
        "keccak_special5",
        DelegationCircuitType::KeccakSpecial5,
        compiled_circuit,
        &buffer,
        &oracle,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}
