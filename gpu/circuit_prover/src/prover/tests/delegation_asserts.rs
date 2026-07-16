use super::*;

pub(super) fn assert_delegation_workflow_matches_cpu<W, O, F>(
    label: &str,
    circuit_type: DelegationCircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    buffer: &[W],
    oracle: &O,
    witness_eval_fn: for<'a> fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<'a, O, BF>,
    ),
    table_driver: &TableDriver<BF>,
    build_gpu_trace: F,
) where
    W: Copy,
    O: cs::oracle::Oracle<BF>,
    F: FnOnce(crate::primitives::context::DeviceAllocation<W>) -> TracingDataDevice,
{
    let worker = Worker::new_with_num_threads(8);
    let trace_len = compiled_circuit.trace_len;
    let prover_config = delegation_prover_config(circuit_type);
    let whir_schedule = prover_config.whir_schedule.clone();
    let external_challenges = test_external_challenges();
    let num_calls = buffer.len();

    let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
        &compiled_circuit,
        circuit_type.get_domain_size(),
        oracle,
        &worker,
        Global,
        Global,
    );
    let full_trace = evaluate_gkr_witness_for_delegation_circuit(
        &compiled_circuit,
        witness_eval_fn,
        circuit_type.get_domain_size(),
        oracle,
        table_driver,
        &worker,
        Global,
        Global,
    );
    ensure_memory_trace_consistency(&memory_trace, &full_trace);

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let setup = CpuGKRSetup::construct(table_driver, &[], trace_len, &compiled_circuit);
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
    let _h2d = crate::prover::transfer::single_shot_h2d(
        |t| gpu_setup_transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let cpu_setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    let gpu_setup_caps = gpu_setup_transfer
        .trace_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    assert_eq!(
        gpu_setup_caps, cpu_setup_caps,
        "{label}: setup caps diverged"
    );

    let trace_data = upload_slice_to_device_for_test(buffer, &context);
    let gpu_trace = build_gpu_trace(trace_data);

    let mut stage1_output = generate_stage1_output_for_test(
        CircuitType::Delegation(circuit_type),
        &compiled_circuit,
        &gpu_setup_transfer,
        None,
        None,
        &gpu_trace,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let (gpu_memory_caps, _gpu_memory_commitment_ms) = commit_memory(
        CircuitType::Delegation(circuit_type),
        &compiled_circuit,
        None,
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
            circuit_type.get_domain_size(),
            &context,
        )
        .unwrap_or_else(|| "no flat-column mismatch found despite cap divergence".to_string());
        panic!("{label}: memory caps diverged; first flat mismatch: {first_mismatch}");
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
            circuit_type.get_domain_size(),
            &context,
        )
        .unwrap_or_else(|| "no flat-column mismatch found despite cap divergence".to_string());
        panic!("{label}: witness caps diverged; first flat mismatch: {first_mismatch}");
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
        "{label}: range-check mappings diverged"
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
        "{label}: timestamp mappings diverged"
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
            circuit_type.get_domain_size(),
            &context,
        );
        assert!(
            first_mismatch.is_none(),
            "{label}: generic lookup multiplicity columns diverged: {}",
            first_mismatch.unwrap()
        );
    }

    let mut cpu_transcript_input = Vec::new();
    external_challenges.flatten_into_buffer(&mut cpu_transcript_input);
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &setup_commitment.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &mem_oracle.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &wit_oracle.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );

    let mut gpu_transcript_input = Vec::new();
    external_challenges.flatten_into_buffer(&mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_setup_caps.into_iter(), &mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_memory_caps.into_iter(), &mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_witness_caps.into_iter(), &mut gpu_transcript_input);

    assert_eq!(
        gpu_transcript_input, cpu_transcript_input,
        "{label}: initial transcript input diverged",
    );

    let mut cpu_seed = Transcript::commit_initial(&cpu_transcript_input);
    let mut gpu_seed = Transcript::commit_initial(&gpu_transcript_input);
    assert_eq!(
        gpu_seed, cpu_seed,
        "{label}: initial transcript seed diverged"
    );

    let cpu_lookup_challenges = draw_random_field_els::<BF, E4>(&mut cpu_seed, 3);
    let gpu_lookup_challenges = draw_random_field_els::<BF, E4>(&mut gpu_seed, 3);
    assert_eq!(
        gpu_lookup_challenges, cpu_lookup_challenges,
        "{label}: lookup challenges diverged after matching transcript inputs",
    );

    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge]: [E4; 3] =
        cpu_lookup_challenges.try_into().unwrap();
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
        "{label}: preprocessed generic lookup diverged: {}",
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

    let final_trace_size_log_2 = 4;
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            &compiled_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            &worker,
        );
    let output_layer_for_sumcheck = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    let (final_explicit_evaluations, evals_flattened) = collect_final_explicit_evaluations_for_test(
        &gkr_storage,
        output_layer_for_sumcheck,
        1 << final_trace_size_log_2,
    );

    let (gpu_forward_output, gpu_transcript_handoff) = {
        let gpu_forward_output = schedule_forward_pass(
            &gpu_setup_transfer,
            &mut stage1_output,
            &mut gpu_forward_setup,
            &compiled_circuit,
            &external_challenges,
            final_trace_size_log_2,
            &context,
        )
        .unwrap();
        let gpu_transcript_handoff = gpu_forward_output
            .schedule_transcript_handoff(true, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        (gpu_forward_output, gpu_transcript_handoff)
    };
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();
    drop(gpu_transcript_handoff);

    assert!(!stage1_output.lookup_mappings.has_generic_family());
    assert!(!stage1_output.lookup_mappings.has_range_check_16());
    assert!(!stage1_output.lookup_mappings.has_timestamp());
    assert!(!gpu_forward_setup.has_generic_lookup());
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
    assert_eq!(gpu_final_explicit_evaluations, final_explicit_evaluations);
    assert_eq!(gpu_evals_flattened, evals_flattened);
}

pub(super) fn assert_bigint_delegation_workflow_matches_cpu(
    compiled_circuit: GKRCircuitArtifact<BF>,
    zero_call: bool,
) {
    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );

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
    assert_delegation_workflow_matches_cpu(
        "bigint_with_control",
        DelegationCircuitType::BigIntWithControl,
        compiled_circuit,
        &buffer,
        &oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        &table_driver,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::BigIntWithControl(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}

pub(super) fn assert_blake2_delegation_workflow_matches_cpu(
    compiled_circuit: GKRCircuitArtifact<BF>,
    zero_call: bool,
) {
    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(
        &mut table_driver,
    );

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
    assert_delegation_workflow_matches_cpu(
        "blake2_with_compression",
        DelegationCircuitType::Blake2WithCompression,
        compiled_circuit,
        &buffer,
        &oracle,
        blake2_with_extended_control_mod::witness_eval_fn,
        &table_driver,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::Blake2WithCompression(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}

pub(super) fn assert_keccak_delegation_workflow_matches_cpu(
    compiled_circuit: GKRCircuitArtifact<BF>,
) {
    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );

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
        !compiled_circuit
            .memory_layout
            .indirect_access_variable_offsets
            .is_empty(),
        "keccak layout must expose variable-offset columns",
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
    assert_delegation_workflow_matches_cpu(
        "keccak_special5",
        DelegationCircuitType::KeccakSpecial5,
        compiled_circuit,
        &buffer,
        &oracle,
        keccak_special5_mod::witness_eval_fn,
        &table_driver,
        |tracing_data| {
            TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(
                crate::witness::trace_delegation::DelegationTraceDevice { tracing_data },
            ))
        },
    );
}
