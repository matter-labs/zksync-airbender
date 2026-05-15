use super::*;

pub(super) fn default_fixture_device_allocator_block_log_size() -> u32 {
    crate::primitives::context::ProverContextConfig::default().allocator_block_log_size
}

pub(super) fn prepare_basic_unrolled_fixture(
    build_config: BasicUnrolledFixtureBuildConfig<'_>,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;
    const DEVICE_ALLOCATOR_ARENA_BYTES: usize = 64usize << 30;
    const HOST_POOL_SIZE_MB: usize = 1024;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;

    let binary = std::fs::read(test_artifact_path(build_config.binary_path)).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section = std::fs::read(test_artifact_path(build_config.text_path)).unwrap();
    assert_eq!(text_section.len() % 4, 0);
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

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism =
        QuasiUARTSource::new_with_reads(build_config.non_determinism_reads.to_vec());

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

    let compiled_circuit: GKRCircuitArtifact<BF> =
        deserialize_json_for_test(build_config.layout_path);

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
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
    drop(replay_ram);
    drop(snapshotter);
    drop(ram);
    drop(non_determinism);
    drop(tape);
    drop(instructions);
    drop(text_section);
    drop(binary);

    let decoder_table_data = preprocessing_data
        .remove(&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX)
        .expect("fixture must contain preprocessed data for the add/sub family");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    drop(preprocessing_data);

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

    let fixture_circuit_type = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
    ));
    let prover_config = fixture_circuit_type
        .prover_config(SecurityLevel::Sec80)
        .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &compiled_circuit,
    );
    assert!(
        build_config.device_allocator_block_log_size >= 4,
        "basic unrolled fixture requires a device allocator block log size of at least 4 for aligned GPU allocations, got {}",
        build_config.device_allocator_block_log_size,
    );
    let device_block_size = 1usize << build_config.device_allocator_block_log_size;
    let max_device_allocation_blocks_count = DEVICE_ALLOCATOR_ARENA_BYTES / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        build_config.device_allocator_block_log_size,
    );
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            whir_schedule.base_lde_factor.trailing_zeros(),
            1,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );
    let decoder_table_host = make_decoder_table_host_for_test(&witness_gen_data);
    eprintln!("fixture: decoder host ready");

    let expected_cpu_proof = if build_config.compute_cpu_reference {
        let worker = Worker::new_with_num_threads(8);
        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
            default_pc_value_in_padding: 4,
        };

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
            add_sub_lui_auipc_mod::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &TableDriver::new(),
            &worker,
            Global,
            Global,
        );
        ensure_memory_trace_consistency(&memory_trace, &full_trace);
        drop(memory_trace);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let setup_commitment = setup.commit(
            &twiddles,
            whir_schedule.base_lde_factor,
            whir_schedule.whir_steps_schedule[0],
            whir_schedule.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );
        let expected_cpu_proof = prove_configured_with_gkr::<BF, E4, DefaultTreeConstructor>(
            &compiled_circuit,
            &external_challenges,
            full_trace,
            &setup,
            &setup_commitment,
            &twiddles,
            &prover_config,
            vec![],
            trace_len,
            &worker,
        );
        eprintln!("fixture: cpu proof ready");
        Some(expected_cpu_proof)
    } else {
        None
    };

    let tracing_data_host = make_non_memory_tracing_host_for_test(buffer);
    eprintln!("fixture: tracing host ready");

    let compute_memory_tree_caps_for_fixture = || {
        let mut setup_transfer =
            GpuGKRSetupTransfer::new(Arc::clone(&gpu_setup_host), &context).unwrap();
        let mut decoder_transfer = if compiled_circuit.has_decoder_lookup {
            Some(DecoderTableTransfer::new(Arc::clone(&decoder_table_host), &context).unwrap())
        } else {
            None
        };
        let mut tracing_data_transfer =
            TracingDataTransfer::new(tracing_data_host.clone(), &context).unwrap();

        setup_transfer.schedule_transfer(&context).unwrap();
        if let Some(decoder_transfer) = decoder_transfer.as_mut() {
            decoder_transfer.schedule_transfer(&context).unwrap();
        }
        tracing_data_transfer.schedule_transfer(&context).unwrap();

        setup_transfer.ensure_transferred(&context).unwrap();
        if let Some(decoder_transfer) = decoder_transfer.as_ref() {
            decoder_transfer
                .transfer
                .ensure_transferred(&context)
                .unwrap();
        }
        tracing_data_transfer
            .transfer
            .ensure_transferred(&context)
            .unwrap();

        let job = commit_memory(
            fixture_circuit_type,
            &compiled_circuit,
            decoder_transfer.as_ref().map(|t| &t.data_device[..]),
            &tracing_data_transfer.data_device,
            &prover_config,
            &context,
        )
        .unwrap();
        let (tree_caps, _) = job.finish().unwrap();
        tree_caps
    };

    // Extract per-coset memory tree caps from the CPU proof (needed for the new prove signature).
    let memory_tree_caps = if let Some(ref cpu_proof) = expected_cpu_proof {
        let combined_cap = &cpu_proof.whir_proof.memory_commitment.commitment.cap;
        let lde_factor = whir_schedule.base_lde_factor;
        let subcap_size = combined_cap.cap.len() / lde_factor;
        combined_cap
            .cap
            .chunks_exact(subcap_size)
            .map(|chunk| MerkleTreeCapVarLength {
                cap: chunk.to_vec(),
            })
            .collect_vec()
    } else {
        compute_memory_tree_caps_for_fixture()
    };

    (
        BasicUnrolledFixture {
            context,
            circuit_type: fixture_circuit_type,
            compiled_circuit,
            external_challenges,
            prover_config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host,
            decoder_table_host,
            tracing_data_host,
            memory_tree_caps,
        },
        expected_cpu_proof,
    )
}

pub(crate) fn prepare_basic_unrolled_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: true,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
        });
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected_cpu_proof
            .expect("proof fixture must include the CPU reference proof"),
    }
}

pub(super) fn prepare_basic_unrolled_profiling_fixture() -> BasicUnrolledFixture {
    let (fixture, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: "examples/basic_fibonacci/app.bin",
            text_path: "examples/basic_fibonacci/app.text",
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            non_determinism_reads: &[],
            compute_cpu_reference: false,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
        });
    assert!(
        expected_cpu_proof.is_none(),
        "profiling fixture must not compute the CPU reference proof",
    );
    fixture
}

pub(crate) struct BasicUnrolledAsyncBackwardFixture {
    pub(crate) context: ProverContext,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) gpu_backward_state: GpuGKRDimensionReducingBackwardState<BF, E4>,
    pub(crate) initial_output_layer_idx: usize,
    pub(crate) top_layer_claims: BTreeMap<GKRAddress, E4>,
    pub(crate) evaluation_point: Vec<E4>,
    pub(crate) seed: Seed,
    pub(crate) batching_challenge: E4,
    pub(crate) lookup_multiplicative_part: E4,
    pub(crate) lookup_additive_part: E4,
    #[allow(dead_code)]
    pub(crate) constraints_batch_challenge: E4,
    pub(crate) expected_proof_layers: usize,
}

pub(super) fn build_basic_unrolled_async_backward_fixture_from_base(
    base: &BasicUnrolledFixture,
) -> BasicUnrolledAsyncBackwardFixture {
    let worker = Worker::new_with_num_threads(8);
    let context = make_test_context(64 * 1024, 1024);
    let mut transfers = base.create_transfers_for_context(&context).unwrap();
    transfers.schedule(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: transfers ready");

    let mut stage1_output = generate_stage1_output_for_test(
        base.circuit_type,
        &base.compiled_circuit,
        &transfers.setup_transfer,
        transfers
            .decoder_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device[..]),
        None,
        &transfers.tracing_data_transfer.data_device,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: stage1 ready");

    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let mut transcript_input = vec![];
    base.external_challenges
        .flatten_into_buffer(&mut transcript_input);
    flatten_merkle_caps_iter_into(
        transfers
            .setup_transfer
            .trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
            .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        base.memory_tree_caps.clone().into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        stage1_output
            .witness_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
            .into_iter(),
        &mut transcript_input,
    );
    let mut seed = Transcript::commit_initial(&transcript_input);
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();
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
    let mut gpu_forward_setup = transfers
        .setup_transfer
        .schedule_forward_setup(
            &base.compiled_circuit,
            upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
            &context,
        )
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: forward setup ready");

    let gpu_forward_output = schedule_forward_pass(
        &transfers.setup_transfer,
        &mut stage1_output,
        &mut gpu_forward_setup,
        &base.compiled_circuit,
        &base.external_challenges,
        base.final_trace_size_log_2,
        &context,
    )
    .unwrap();
    eprintln!("async-backward-from-base: forward pass scheduled");
    let gpu_transcript_handoff = gpu_forward_output
        .schedule_transcript_handoff(true, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: transcript handoff ready");
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();

    commit_field_els::<BF, E4>(&mut seed, &gpu_evals_flattened);
    let mut challenges =
        draw_random_field_els::<BF, E4>(&mut seed, base.final_trace_size_log_2 + 1);
    let batching_challenge = challenges.pop().unwrap();
    let evaluation_point = challenges;

    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        compute_initial_sumcheck_claims_from_explicit_evaluations_for_test(
            &gpu_final_explicit_evaluations,
            &evaluation_point,
            &worker,
        );

    let output_layer_for_sumcheck = gpu_forward_output
        .dimension_reducing_inputs
        .get(&gpu_forward_output.initial_layer_for_sumcheck)
        .unwrap();
    let mut top_layer_claims = BTreeMap::new();
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    let expected_proof_layers =
        gpu_forward_output.dimension_reducing_inputs.len() + base.compiled_circuit.layers.len();
    let initial_output_layer_idx = gpu_forward_output.initial_layer_for_sumcheck + 1;

    drop(gpu_transcript_handoff);
    drop(gpu_forward_setup);
    drop(transfers);
    drop(stage1_output);

    BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit: base.compiled_circuit.clone(),
        external_challenges: base.external_challenges,
        gpu_backward_state: gpu_forward_output.into_dimension_reducing_backward_state(),
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_multiplicative_part: lookup_alpha,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers,
    }
}

pub(crate) fn prepare_basic_unrolled_async_backward_fixture(
    _final_trace_size_log_2: usize,
) -> BasicUnrolledAsyncBackwardFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: false,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
        });
    assert!(
        expected_cpu_proof.is_none(),
        "async backward fixture must not compute the CPU reference proof",
    );
    build_basic_unrolled_async_backward_fixture_from_base(&base)
}
