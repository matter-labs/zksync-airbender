use super::*;

#[test]
#[serial]
fn run_basic_unrolled_stagewise_parity_test() {
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
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
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
    let total_shuffle_entries: usize = shuffle_ram_touched_addresses.iter().map(Vec::len).sum();
    assert_ne!(
        total_shuffle_entries, 0,
        "expected RAM touches for stagewise parity test"
    );

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

    // evaluate memory witness
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

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let decoder_table_data = &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
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
    let add_sub_circuit_type = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
    ));
    let prover_config = add_sub_circuit_type
        .prover_config(SecurityLevel::Sec80)
        .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let base_lde_factor = whir_schedule.base_lde_factor;
    let tree_cap_size = whir_schedule.cap_size;
    let setup = CpuGKRSetup::construct(
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
    let context = make_test_context(64 * 1024, 1024);
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
    {
        let _range = scoped_range(None, "test.gpu.setup_transfer");
        let _h2d = crate::primitives::transfer::single_shot_h2d(
            |t| gpu_setup_transfer.schedule_transfer(t, &context),
            &context,
        )
        .unwrap();
        context.get_h2d_stream().synchronize().unwrap();
    }

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

    let trace_holder_caps = gpu_setup_transfer
        .trace_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    let setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    assert_eq!(trace_holder_caps, setup_caps);
    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(|d| d.into())
        .collect_vec();
    let d_decoder_table = upload_slice_to_device_for_test(&h_decoder_table, &context);
    let trace_data = upload_slice_to_device_for_test(&buffer, &context);
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(
        UnrolledNonMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));
    let mut stage1_output = {
        let _range = scoped_range(None, "test.gpu.stage1.generate");
        let stage1_output = generate_stage1_output_for_test(
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            &add_sub_circuit,
            &gpu_setup_transfer,
            if add_sub_circuit.has_decoder_lookup {
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
        stage1_output
    };

    // Stage1 does not commit memory traces in production; this parity test needs the
    // memory caps later for the WHIR helper, so materialize them explicitly here.
    stage1_output
        .memory_trace_holder
        .commit_all(&context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let memory_caps = stage1_caps_from_tree(&mem_oracle.tree, subcap_size);
    assert_eq!(
        stage1_output
            .memory_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap(),
        memory_caps
    );

    let witness_caps = stage1_caps_from_tree(&wit_oracle.tree, subcap_size);
    assert_eq!(
        stage1_output
            .witness_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap(),
        witness_caps
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

    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let lookup_challenges = [
        lookup_alpha,
        lookup_additive_part,
        constraints_batch_challenge,
    ];
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&lookup_challenges);
    }
    let mut gpu_forward_setup = {
        let _range = scoped_range(None, "test.gpu.forward_setup.schedule");
        let gpu_forward_setup = gpu_setup_transfer
            .schedule_forward_setup(
                &add_sub_circuit,
                upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
                &context,
            )
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        gpu_forward_setup
    };

    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    insert_virtual_setup_polys_for_test(trace_len, &mut gkr_storage);
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(
            &add_sub_circuit,
            lookup_alpha,
            trace_len,
            &mut gkr_storage,
            &worker,
        );

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &add_sub_circuit,
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
            &add_sub_circuit,
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
        let _range = scoped_range(None, "test.gpu.forward.schedule");
        let gpu_forward_output = schedule_forward_pass(
            &gpu_setup_transfer,
            &mut stage1_output,
            &mut gpu_forward_setup,
            &add_sub_circuit,
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
    {
        let _range = scoped_range(None, "test.gpu.forward.readback_asserts");
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
        assert_eq!(gpu_final_explicit_evaluations, final_explicit_evaluations);
        assert_eq!(gpu_evals_flattened, evals_flattened);
    }
    drop(gpu_forward_setup);

    let (copy_input, copy_output) = add_sub_circuit
        .layers
        .iter()
        .flat_map(|layer| {
            layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
        })
        .find_map(|gate| match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => Some((*input, *output)),
            _ => None,
        })
        .expect("test circuit must contain a Copy relation");
    if let Some(input_poly) = gpu_forward_output.storage.try_get_base_poly(copy_input) {
        let output_poly = gpu_forward_output
            .storage
            .try_get_base_poly(copy_output)
            .expect("copy output must preserve base-field representation");
        assert!(input_poly.shares_backing_with(output_poly));
    } else {
        let input_poly = gpu_forward_output
            .storage
            .try_get_ext_poly(copy_input)
            .expect("copy input must exist");
        let output_poly = gpu_forward_output
            .storage
            .try_get_ext_poly(copy_output)
            .expect("copy output must preserve extension-field representation");
        assert!(input_poly.shares_backing_with(output_poly));
    }

    let seed_before_explicit_commit = seed;
    commit_field_els::<BF, E4>(&mut seed, &evals_flattened);
    let seed_after_cpu_explicit_commit = seed;

    let mut gpu_seed = seed_before_explicit_commit;
    commit_field_els::<BF, E4>(&mut gpu_seed, &gpu_evals_flattened);
    assert_eq!(gpu_seed, seed_after_cpu_explicit_commit);

    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges = draw_random_field_els::<BF, E4>(&mut seed, num_challenges);
    let expected_challenges = challenges.clone();
    let mut gpu_challenges = draw_random_field_els::<BF, E4>(&mut gpu_seed, num_challenges);
    assert_eq!(gpu_challenges, expected_challenges);
    let batching_challenge = challenges.pop().unwrap();
    let gpu_batching_challenge = gpu_challenges.pop().unwrap();
    assert_eq!(gpu_batching_challenge, batching_challenge);

    let evaluation_point = challenges;
    let gpu_evaluation_point = gpu_challenges;
    assert_eq!(gpu_evaluation_point, evaluation_point);
    assert_eq!(gpu_seed, seed);
    let backward_initial_seed = seed;
    let cpu_initial_claims = compute_initial_sumcheck_claims_for_test(
        &gkr_storage,
        &evaluation_point,
        output_layer_for_sumcheck,
        &worker,
    );
    let gpu_initial_claims = compute_initial_sumcheck_claims_from_explicit_evaluations_for_test(
        &gpu_final_explicit_evaluations,
        &evaluation_point,
        &worker,
    );
    assert_eq!(gpu_initial_claims, cpu_initial_claims);
    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        cpu_initial_claims;
    let gpu_backward_state = gpu_forward_output.into_dimension_reducing_backward_state();

    let output_map = output_layer_for_sumcheck;
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
    claims_for_layers.insert(initial_layer_for_sumcheck + 1, top_layer_claims.clone());
    points_for_claims_at_layer.insert(initial_layer_for_sumcheck + 1, evaluation_point.clone());

    let mut sumcheck_intermediate_values = BTreeMap::new();
    let mut sumcheck_batching_challenge = batching_challenge;
    let mut reduced_trace_size_log_2 = final_trace_size_log_2;
    {
        let _range = scoped_range(None, "test.cpu.sumcheck.dimension_reduction");
        for (layer_idx, layer) in dimension_reducing_inputs.into_iter().rev() {
            let _layer_range = scoped_range(
                None,
                &format!("test.cpu.sumcheck.dimension_reduction.layer.{layer_idx}"),
            );
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
    }

    assert_eq!(1 << reduced_trace_size_log_2, trace_len);

    {
        let _range = scoped_range(None, "test.cpu.sumcheck.main_layers");
        for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate().rev() {
            let _layer_range = scoped_range(
                None,
                &format!("test.cpu.sumcheck.main_layers.layer.{layer_idx}"),
            );

            let proof = sumcheck_loop::evaluate_sumcheck_for_layer(
                layer_idx,
                layer,
                &mut points_for_claims_at_layer,
                &mut claims_for_layers,
                &mut gkr_storage,
                &mut sumcheck_batching_challenge,
                &add_sub_circuit,
                trace_len,
                lookup_alpha,
                lookup_additive_part,
                &[],
                0,
                &external_challenges,
                &mut seed,
                &worker,
            );
            sumcheck_intermediate_values.insert(layer_idx, proof);
        }
    }

    // Build a real proof layout so the backward scheduler can write per-layer
    // sumcheck coefficients and final-step evaluations into the slab. The
    // stagewise test never reads from the slab — it compares against CPU via
    // `claims_for_layers` / `points_for_claims_at_layer` — but the scheduler
    // indexes `proof_layout.backward[layer_slot]` unconditionally.
    let memory_geometry = crate::prover::proof::layout::ProofLayoutBaseLayerGeometry::from_geometry(
        GpuGKRTraceGeometry {
            log_domain_size: stage1_output.memory_trace_holder.log_domain_size,
            log_lde_factor: stage1_output.memory_trace_holder.log_lde_factor,
            log_rows_per_leaf: stage1_output.memory_trace_holder.log_rows_per_leaf,
            log_tree_cap_size: stage1_output.memory_trace_holder.log_tree_cap_size,
        },
        stage1_output.memory_trace_holder.columns_count,
    );
    let witness_geometry =
        crate::prover::proof::layout::ProofLayoutBaseLayerGeometry::from_geometry(
            GpuGKRTraceGeometry {
                log_domain_size: stage1_output.witness_trace_holder.log_domain_size,
                log_lde_factor: stage1_output.witness_trace_holder.log_lde_factor,
                log_rows_per_leaf: stage1_output.witness_trace_holder.log_rows_per_leaf,
                log_tree_cap_size: stage1_output.witness_trace_holder.log_tree_cap_size,
            },
            stage1_output.witness_trace_holder.columns_count,
        );
    let setup_geometry_dims =
        crate::prover::proof::layout::ProofLayoutBaseLayerGeometry::from_geometry(
            GpuGKRTraceGeometry {
                log_domain_size: gpu_setup_transfer.trace_holder.log_domain_size,
                log_lde_factor: gpu_setup_transfer.trace_holder.log_lde_factor,
                log_rows_per_leaf: gpu_setup_transfer.trace_holder.log_rows_per_leaf,
                log_tree_cap_size: gpu_setup_transfer.trace_holder.log_tree_cap_size,
            },
            gpu_setup_transfer.trace_holder.columns_count,
        );
    let proof_layout_inputs = crate::prover::proof::layout::build_proof_layout_inputs::<E4>(
        &add_sub_circuit,
        &external_challenges,
        &whir_schedule,
        final_trace_size_log_2,
        memory_geometry,
        witness_geometry,
        setup_geometry_dims,
    );
    let proof_layout = ProofLayout::new(&proof_layout_inputs);
    assert!(
        proof_layout.total_bytes > 0,
        "proof layout must have non-zero bytes",
    );
    assert_eq!(
        proof_layout.total_bytes % std::mem::size_of::<E4>(),
        0,
        "proof slab size must be E4-aligned",
    );
    let proof_slab: crate::primitives::context::DeviceAllocation<E4> = context
        .alloc_with_extra_alignment::<E4, 4>(
            proof_layout.total_bytes / std::mem::size_of::<E4>(),
            crate::allocator::tracker::AllocationPlacement::Bottom,
        )
        .unwrap();
    let mut gpu_backward_execution = {
        let _range = scoped_range(None, "test.gpu.sumcheck.backward_workflow");
        gpu_backward_state
            .schedule_execute_backward_workflow(
                add_sub_circuit.clone(),
                external_challenges.clone(),
                initial_layer_for_sumcheck + 1,
                top_layer_claims.clone(),
                evaluation_point.clone(),
                backward_initial_seed,
                batching_challenge,
                lookup_alpha,
                lookup_additive_part,
                &proof_slab,
                &proof_layout,
                &context,
            )
            .unwrap()
            .wait(&context)
            .unwrap()
    };

    // Per-layer sumcheck intermediate proof values are no longer exposed on the
    // backward scheduler — they live in the device-resident proof slab and are
    // parsed by the full `prove()` assembly path, which the end-to-end CPU parity
    // tests (`run_basic_unrolled_test`, `run_basic_unrolled_proof_job_multi_schedule_test`)
    // exercise directly.
    assert_layer_points_eq_for_test(
        &gpu_backward_execution.points_for_claims_at_layer,
        &points_for_claims_at_layer,
    );
    assert_backward_claims_eq_before_base_layer_expansion(
        &gpu_backward_execution.claims_for_layers,
        &claims_for_layers,
    );
    assert_eq!(
        gpu_backward_execution
            .points_for_claims_at_layer
            .get(&1)
            .cloned(),
        points_for_claims_at_layer.get(&1).cloned(),
        "layer 1 claim point diverged before layer-0 proof comparison"
    );
    assert_eq!(
        gpu_backward_execution.claims_for_layers.get(&1).cloned(),
        claims_for_layers.get(&1).cloned(),
        "layer 1 claims diverged before layer-0 proof comparison"
    );
    assert_eq!(
        gpu_backward_execution.next_batching_challenge,
        sumcheck_batching_challenge
    );

    let base_layer_z = gpu_backward_execution
        .points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point");
    let raw_gpu_base_layer_claims = gpu_backward_execution
        .claims_for_layers
        .get(&0)
        .cloned()
        .expect("must have raw layer-0 claims after backward");
    let eq_precomputed = make_eq_poly_in_full(base_layer_z, &worker);
    let eq_at_z = eq_precomputed.last().unwrap();
    let layer_desc = &add_sub_circuit.layers[0];

    let (
        cpu_base_layer_claims,
        cpu_extra_evaluations_from_caching_relations,
        _cpu_extra_evaluations_transcript_batches,
        cpu_mem_polys_claims,
        cpu_wit_polys_claims,
        cpu_setup_polys_claims,
    ) = {
        let mut cpu_base_layer_claims = raw_gpu_base_layer_claims.clone();
        let mut cpu_extra_evaluations_from_caching_relations = BTreeMap::new();
        let mut cpu_extra_evaluations_transcript_batches = Vec::new();
        for (cached_addr, relation) in layer_desc.cached_relations.iter() {
            debug_assert!(
                cpu_base_layer_claims.contains_key(cached_addr),
                "Missing claim for cached address {:?}",
                cached_addr
            );

            for dep in relation.dependencies() {
                if cpu_base_layer_claims.contains_key(&dep) {
                    continue;
                }
                match dep {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_) => {
                        let values = gkr_storage.get_base_layer(dep);
                        let evaluation = evaluate_base_poly_with_eq::<BF, E4>(values, &eq_at_z[..]);
                        cpu_base_layer_claims.insert(dep, evaluation);
                        cpu_extra_evaluations_from_caching_relations.insert(dep, evaluation);
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

        if !cpu_extra_evaluations_from_caching_relations.is_empty() {
            cpu_extra_evaluations_transcript_batches.push(
                cpu_extra_evaluations_from_caching_relations
                    .values()
                    .copied()
                    .collect_vec(),
            );
        }

        let mut mem_polys_claims = Vec::with_capacity(add_sub_circuit.memory_layout.total_width);
        for i in 0..add_sub_circuit.memory_layout.total_width {
            let key = GKRAddress::BaseLayerMemory(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            mem_polys_claims.push(evaluation);
        }

        let mut wit_polys_claims = Vec::with_capacity(add_sub_circuit.witness_layout.total_width);
        for i in 0..add_sub_circuit.witness_layout.total_width {
            let key = GKRAddress::BaseLayerWitness(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            wit_polys_claims.push(evaluation);
        }

        let mut setup_polys_claims = Vec::with_capacity(setup.hypercube_evals.len());
        for i in 0..setup.hypercube_evals.len() {
            let key = GKRAddress::Setup(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            setup_polys_claims.push(evaluation);
        }

        for virtual_setup_poly in [
            VirtualSetupPoly::RangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow,
            VirtualSetupPoly::InitsAndTeardownsHigh,
        ] {
            let key = GKRAddress::VirtualSetup(virtual_setup_poly);
            if cpu_base_layer_claims.contains_key(&key) {
                continue;
            }

            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            cpu_base_layer_claims.insert(key, evaluation);
        }

        (
            cpu_base_layer_claims,
            cpu_extra_evaluations_from_caching_relations,
            cpu_extra_evaluations_transcript_batches,
            mem_polys_claims,
            wit_polys_claims,
            setup_polys_claims,
        )
    };

    // GPU base-layer-claims scheduling is exercised end-to-end via
    // `prove()` smoke tests. Direct host-snapshot comparison against CPU
    // (formerly via `prepare_base_layer_claims`) has been retired alongside
    // the per-column D2H readback path it depended on. Downstream WHIR
    // parity below feeds the CPU-computed claim vectors into both the CPU
    // and GPU code paths so the test continues to verify the WHIR fold.

    // CPU side already merged virtual-setup and cached-relation values into
    // `cpu_base_layer_claims` above; the seed-advance must replay the same
    // host transcript steps the GPU does internally so downstream WHIR
    // setup sees the same seed.
    let mut gpu_seed_after_base_layer_claims = gpu_backward_execution.updated_seed;
    let extras_values_for_seed: Vec<E4> = cpu_extra_evaluations_from_caching_relations
        .values()
        .copied()
        .collect();
    if !extras_values_for_seed.is_empty() {
        commit_field_els::<BF, E4>(
            &mut gpu_seed_after_base_layer_claims,
            &extras_values_for_seed,
        );
    }
    assert_eq!(gpu_seed_after_base_layer_claims, seed);

    drop(preprocessed_generic_lookup);
    // Reconstruct the BTreeMap shape that downstream CPU sumcheck/WHIR setup
    // expects: layer-1 incoming claims (already present) ∪ virtual-setup
    // claims ∪ caching-relations extras. Sourcing from the already-built
    // `cpu_base_layer_claims` map (the same one used as the GPU parity
    // oracle above) keeps the downstream comparisons honest.
    {
        let layer_0_claims = gpu_backward_execution
            .claims_for_layers
            .get_mut(&0)
            .expect("backward main-layer scheduler must populate layer-0 claims");
        for (addr, value) in cpu_base_layer_claims.iter() {
            layer_0_claims.entry(*addr).or_insert(*value);
        }
        for (addr, value) in cpu_extra_evaluations_from_caching_relations.iter() {
            layer_0_claims.insert(*addr, *value);
        }
    }

    drop(gkr_storage);

    let whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
    let whir_schedule = whir_schedule.clone();
    stage1_output
        .memory_trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    stage1_output
        .witness_trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    gpu_setup_transfer
        .trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    // The per-round WHIR check takes tree caps from the trace holders, so we
    // capture the full GPU WHIR proof from this call rather than running a
    // second gpu_whir_fold_supported_path (which would try to take the
    // already-consumed tree caps and panic).
    let gpu_whir_proof = {
        let _range = scoped_range(None, "test.gpu.whir.recursive_oracle_parity");
        assert_recursive_whir_oracle_parity_for_supported_path(
            &mem_oracle,
            &cpu_mem_polys_claims,
            &mut stage1_output.memory_trace_holder,
            &wit_oracle,
            &cpu_wit_polys_claims,
            &mut stage1_output.witness_trace_holder,
            &setup_commitment,
            &cpu_setup_polys_claims,
            &mut gpu_setup_transfer.trace_holder,
            base_layer_z,
            whir_schedule.base_lde_factor,
            whir_batching_challenge,
            &whir_schedule,
            &twiddles,
            seed.clone(),
            trace_len.trailing_zeros() as usize,
            &worker,
            &context,
        )
    };
    let cpu_whir_proof = {
        let _range = scoped_range(None, "test.cpu.whir_fold");
        whir_fold(
            mem_oracle,
            cpu_mem_polys_claims.clone(),
            wit_oracle,
            cpu_wit_polys_claims.clone(),
            &setup_commitment,
            cpu_setup_polys_claims.clone(),
            base_layer_z.clone(),
            whir_batching_challenge,
            &whir_schedule,
            &twiddles,
            seed,
            whir_schedule.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        )
    };
    assert_whir_proof_eq_for_test(&gpu_whir_proof, &cpu_whir_proof);
    let whir_proof = gpu_whir_proof;

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
    let mut grand_product_accumulator_computed = write_set_computed;
    grand_product_accumulator_computed
        .mul_assign(&read_set_computed.inverse().expect("must not be zero"));

    let _proof = GKRProof::<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        external_challenges,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        whir_proof,
        grand_product_accumulator_computed,
        inits_and_teardowns_top_bits: (0..add_sub_circuit.memory_layout.teardown_sets.len() as u32)
            .collect(),
    };
    let _elapsed = now.elapsed();
}
