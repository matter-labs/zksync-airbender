use super::*;

pub(super) fn add_mem_word_only_tables_for_test(
    table_driver: &mut TableDriver<BF>,
    binary: &[u32],
) {
    mem_word_only_table_driver_fn(table_driver);
    for (table_type, table) in
        create_mem_word_only_special_tables::<_, { ROM_SECOND_WORD_BITS }>(binary)
    {
        table_driver.add_table_with_content(table_type, table);
    }
}

pub(super) fn add_mem_subword_only_tables_for_test(
    table_driver: &mut TableDriver<BF>,
    binary: &[u32],
) {
    mem_subword_only_table_driver_fn(table_driver);
    for (table_type, table) in
        create_mem_subword_only_special_tables::<_, { ROM_SECOND_WORD_BITS }>(binary)
    {
        table_driver.add_table_with_content(table_type, table);
    }
}

pub(super) fn compile_mem_word_only_circuit_for_test(binary: &[u32]) -> GKRCircuitArtifact<BF> {
    let extra_tables = create_mem_word_only_special_tables::<_, { ROM_SECOND_WORD_BITS }>(binary);
    compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| {
            mem_word_only_table_addition_fn(cs);
            for (table_type, table) in extra_tables.clone() {
                cs.add_table_with_content(table_type, table);
            }
        },
        &|cs| mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        24,
    )
}

pub(super) fn compile_mem_subword_only_circuit_for_test(binary: &[u32]) -> GKRCircuitArtifact<BF> {
    let extra_tables =
        create_mem_subword_only_special_tables::<_, { ROM_SECOND_WORD_BITS }>(binary);
    compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| {
            mem_subword_only_table_addition_fn(cs);
            for (table_type, table) in extra_tables.clone() {
                cs.add_table_with_content(table_type, table);
            }
        },
        &|cs| mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        24,
    )
}

pub(super) fn run_memory_workflow_input_parity_test<const FAMILY_IDX: u8>(
    family_label: &str,
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: &[u32],
    circuit_type: UnrolledMemoryCircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            MemoryCircuitOracle<'_>,
            BF,
        >,
    ),
    populate_table_driver: fn(&mut TableDriver<BF>, &[u32]),
) {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let binary = read_test_words(binary_path);
    let text_section = read_test_words(text_path);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_reads.to_vec());

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    assert!(
        num_calls > 0,
        "expected selected workload to exercise the {family_label} family"
    );
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

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

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut replay_state,
        &mut replay_ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, replay_state);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
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
    let decoder_table_data = &preprocessing_data[&FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let oracle = MemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
    };
    let mut table_driver = TableDriver::new();
    populate_table_driver(&mut table_driver, &binary);
    let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &compiled_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );
    let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        &compiled_circuit,
        witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        Global,
        Global,
    );
    ensure_memory_trace_consistency(&memory_trace, &full_trace);

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let memory_circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type));
    let prover_config = memory_circuit_type
        .prover_config(SecurityLevel::Sec80)
        .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        trace_len,
        &compiled_circuit,
    );
    let setup_commitment = setup.commit::<DefaultTreeConstructor>(
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let subcap_size = whir_schedule.cap_size / whir_schedule.base_lde_factor;
    let context = make_test_context(64 * 1024, 1024);
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            whir_schedule.base_lde_factor.trailing_zeros(),
            whir_schedule.whir_steps_schedule[0] as u32,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );
    let mut gpu_setup_transfer =
        GpuGKRSetupTransfer::new(Arc::clone(&gpu_setup_host), &context).unwrap();
    gpu_setup_transfer.schedule_transfer(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let cpu_setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    let gpu_setup_caps = gpu_setup_transfer
        .trace_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    assert_eq!(
        gpu_setup_caps, cpu_setup_caps,
        "{family_label} setup caps diverged"
    );

    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect_vec();
    let d_decoder_table = upload_slice_to_device_for_test(&h_decoder_table, &context);
    let trace_data = upload_slice_to_device_for_test(&buffer, &context);
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(
        UnrolledMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));
    let mut stage1_output = generate_stage1_output_for_test(
        CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type)),
        &compiled_circuit,
        &gpu_setup_transfer,
        if compiled_circuit.has_decoder_lookup {
            Some(&d_decoder_table)
        } else {
            None
        },
        None,
        &gpu_trace,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let (gpu_memory_caps, _gpu_memory_commitment_ms) = commit_memory(
        memory_circuit_type,
        &compiled_circuit,
        if compiled_circuit.has_decoder_lookup {
            Some(&d_decoder_table)
        } else {
            None
        },
        &gpu_trace,
        &prover_config,
        &context,
    )
    .unwrap()
    .finish()
    .unwrap();

    let (mem_oracle, wit_oracle) = stage1::stage1::<BF, DefaultTreeConstructor>(
        &full_trace,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let cpu_memory_caps = stage1_caps_from_tree(&mem_oracle.tree, subcap_size);
    if gpu_memory_caps != cpu_memory_caps {
        let first_mismatch = describe_first_trace_holder_column_mismatch(
            &stage1_output.memory_trace_holder,
            &full_trace.column_major_memory_trace,
            NUM_CYCLES_PER_CHUNK,
            &context,
        )
        .unwrap_or_else(|| "no flat-column mismatch found despite cap divergence".to_string());
        panic!("{family_label} memory caps diverged; first flat mismatch: {first_mismatch}");
    }

    assert_generic_family_mapping_contract(
        &stage1_output.lookup_mappings,
        &full_trace,
        num_calls,
        &context,
    );
    let generic_lookup_multiplicities_range = compiled_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .clone();
    if !generic_lookup_multiplicities_range.is_empty() {
        let first_mismatch = describe_first_trace_holder_subrange_mismatch(
            &stage1_output.witness_trace_holder,
            &full_trace.column_major_witness_trace,
            generic_lookup_multiplicities_range.clone(),
            NUM_CYCLES_PER_CHUNK,
            &context,
        );
        assert!(
            first_mismatch.is_none(),
            "{family_label} generic lookup multiplicity columns diverged: {}",
            first_mismatch.unwrap()
        );
    }

    let cpu_witness_caps = stage1_caps_from_tree(&wit_oracle.tree, subcap_size);
    let gpu_witness_caps = stage1_output
        .witness_trace_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    if gpu_witness_caps != cpu_witness_caps {
        let first_mismatch = describe_first_trace_holder_column_mismatch(
            &stage1_output.witness_trace_holder,
            &full_trace.column_major_witness_trace,
            NUM_CYCLES_PER_CHUNK,
            &context,
        )
        .unwrap_or_else(|| "no flat-column mismatch found despite cap divergence".to_string());
        panic!("{family_label} witness caps diverged; first flat mismatch: {first_mismatch}");
    }

    assert_generic_family_mapping_contract(
        &stage1_output.lookup_mappings,
        &full_trace,
        num_calls,
        &context,
    );
    let expected_range_check = full_trace
        .range_check_16_lookup_mapping
        .iter()
        .flat_map(|column| column.iter().map(|value| u32::from(*value)))
        .collect_vec();
    let gpu_range_check =
        copy_u32_device_slice_to_host(stage1_output.lookup_mappings.range_check_16(), &context);
    assert_eq!(
        gpu_range_check, expected_range_check,
        "{family_label} range-check mappings diverged"
    );
    let expected_timestamp = full_trace
        .timestamp_range_check_lookup_mapping
        .iter()
        .flat_map(|column| column.iter().copied())
        .collect_vec();
    let gpu_timestamp =
        copy_u32_device_slice_to_host(stage1_output.lookup_mappings.timestamp(), &context);
    assert_eq!(
        gpu_timestamp, expected_timestamp,
        "{family_label} timestamp mappings diverged"
    );

    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);
    let permutation_argument_linearization_challenges: [E4; NUM_PERMUTATION_ARGUMENT_KEY_PARTS
        - 1] = materialize_powers_serial_starting_with_elem::<_, Global>(
        memory_argument_alpha,
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
    )
    .try_into()
    .unwrap();
    let external_challenges: GKRExternalChallenges<BF, E4> = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    let lookup_alpha = E4::from_array_of_base([BF::new(3), BF::new(5), BF::new(7), BF::new(11)]);
    let lookup_additive_part =
        E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);
    let constraints_batch_challenge =
        E4::from_array_of_base([BF::new(29), BF::new(31), BF::new(37), BF::new(41)]);
    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&[
                lookup_alpha,
                lookup_additive_part,
                constraints_batch_challenge,
            ]);
    }
    let mut gpu_forward_setup = gpu_setup_transfer
        .schedule_forward_setup(
            &compiled_circuit,
            upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
            &context,
        )
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    insert_virtual_setup_polys_for_test(trace_len, &mut gkr_storage);
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(
            &compiled_circuit,
            lookup_alpha,
            trace_len,
            &mut gkr_storage,
            &worker,
        );

    let mut gpu_generic = vec![E4::ZERO; gpu_forward_setup.generic_lookup_len()];
    memory_copy_async(
        &mut gpu_generic,
        gpu_forward_setup.generic_lookup(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let first_mismatch = describe_first_vec_mismatch(&gpu_generic, &preprocessed_generic_lookup);
    assert!(
        first_mismatch.is_none(),
        "{family_label} preprocessed generic lookup diverged: {}",
        first_mismatch.unwrap()
    );

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &compiled_circuit,
            &external_challenges,
            &mut witness_eval_data,
            &[],
            trace_len,
            &preprocessed_generic_lookup,
            lookup_alpha,
            lookup_additive_part,
            decoder_lookup_fill_value,
            &worker,
        );
    }

    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            &compiled_circuit,
            trace_len.trailing_zeros() as usize,
            FINAL_TRACE_SIZE_LOG_2,
            &worker,
        );
    let output_layer_for_sumcheck = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    let (final_explicit_evaluations, evals_flattened) = collect_final_explicit_evaluations_for_test(
        &gkr_storage,
        output_layer_for_sumcheck,
        1 << FINAL_TRACE_SIZE_LOG_2,
    );

    let gpu_forward_output = schedule_forward_pass(
        &gpu_setup_transfer,
        &mut stage1_output,
        &mut gpu_forward_setup,
        &compiled_circuit,
        &external_challenges,
        FINAL_TRACE_SIZE_LOG_2,
        &context,
    )
    .unwrap();
    let gpu_transcript_handoff = gpu_forward_output
        .schedule_transcript_handoff(true, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();
    drop(gpu_transcript_handoff);

    assert_eq!(
        gpu_forward_output.initial_layer_for_sumcheck,
        initial_layer_for_sumcheck
    );
    assert_eq!(
        gpu_forward_output.dimension_reducing_inputs,
        dimension_reducing_inputs
    );
    assert_gpu_and_cpu_gkr_storage_match(
        &gpu_forward_output.storage,
        &gkr_storage,
        &compiled_circuit,
        &context,
    );
    assert_eq!(
        gpu_final_explicit_evaluations, final_explicit_evaluations,
        "{family_label} final explicit evaluations diverged"
    );
    assert_eq!(
        gpu_evals_flattened, evals_flattened,
        "{family_label} flattened transcript evaluations diverged"
    );
}
