use super::*;

use super::inits_and_teardowns::{
    build_inits_and_teardowns_pages_for_test, build_inits_and_teardowns_trace_host_for_test,
};

#[test]
#[serial]
#[ignore]
fn run_unified_stagewise_parity_test() {
    type CountersT = DelegationsAndUnifiedCounters;
    const TRACE_LEN_LOG2: usize = 24;
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let binary = read_test_words("examples/multi_family_smoke/app_blake2_g_function.bin");
    let text_section = read_test_words("examples/multi_family_smoke/app_blake2_g_function.text");
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;
    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]);
    let finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(finished);
    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let compiled_circuit: GKRCircuitArtifact<BF> =
        deserialize_json_for_test("cs/compiled_circuits/unified_reduced_machine_layout_gkr.json");
    let num_unified_teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
    let num_calls = counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();

    let (full_trace, unified_table_driver, buffer, witness_gen_data, sparse_inits_and_teardowns) =
        build_unified_full_trace_for_test(
            &binary,
            &text_section,
            &compiled_circuit,
            &snapshotter,
            &ram,
            &expected_final_state,
            &tape,
            cycles_bound,
            num_unified_teardown_sets,
            num_calls,
            true,
            &worker,
        );

    // Reconstruct the Option decoder table from the oracle (CpuGKRSetup::construct
    // takes &[Option<ExecutorFamilyDecoderData>] to preserve None fill semantics).
    let option_decoder_table = build_unified_decoder_table(&text_section);

    // Build prover config + CPU setup + GPU setup (no commit needed for stage1 parity).
    let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    let prover_config =
        crate::prover::config::prover_config(circuit_type, SecurityLevel::Sec80).unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(
        &unified_table_driver,
        &option_decoder_table,
        trace_len,
        &compiled_circuit,
    );

    let log_lde_factor = whir_schedule.base_lde_factor.trailing_zeros();
    let log_rows_per_leaf = whir_schedule.whir_steps_schedule[0] as u32;
    let log_tree_cap_size = whir_schedule.cap_size.trailing_zeros();

    println!("DEBUG: creating context");
    let context = make_test_context_with_device_allocator_block_log_size(
        // 64 GB device arena, sized to match the unified fixture's arena.
        (64usize << 30) >> default_fixture_device_allocator_block_log_size(),
        1024,
        default_fixture_device_allocator_block_log_size(),
    );
    println!("DEBUG: context created, precomputing setup");
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

    println!("DEBUG: gpu_setup_host precomputed, uploading decoder table");
    // Upload GPU decoder table (unwrapped form, matching the GPU wire format).
    let h_decoder_table: Vec<ExecutorFamilyDecoderData> = witness_gen_data
        .iter()
        .copied()
        .map(|d| d.into())
        .collect_vec();
    let d_decoder_table = upload_slice_to_device_for_test(&h_decoder_table, &context);

    println!(
        "DEBUG: decoder table uploaded, uploading trace buffer (num_calls={}, size_bytes={})",
        buffer.len(),
        buffer.len() * std::mem::size_of::<UnifiedOpcodeTracingDataWithTimestamp>()
    );
    // Build unified trace device.
    let trace_data = upload_slice_to_device_for_test(&buffer, &context);
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(
        UnrolledUnifiedTraceDevice {
            tracing_data: trace_data,
        },
    ));

    println!(
        "DEBUG: trace buffer uploaded, building i/t pages; sparse_sets={}, sparse_entries_total={}",
        sparse_inits_and_teardowns.len(),
        sparse_inits_and_teardowns
            .iter()
            .map(|v| v.len())
            .sum::<usize>()
    );
    // Build inits-and-teardowns device and transfer.
    let (page_indices, values_packed, timestamps_packed) = build_inits_and_teardowns_pages_for_test(
        &sparse_inits_and_teardowns,
        TRACE_LEN_LOG2 as u32,
        num_unified_teardown_sets as u32,
    );
    println!(
        "DEBUG: i/t pages built: num_pages={}, values_bytes={}, timestamps_bytes={}",
        page_indices.len(),
        values_packed.len() * 4,
        timestamps_packed.len() * 8
    );
    let it_host = build_inits_and_teardowns_trace_host_for_test(
        &page_indices,
        &values_packed,
        &timestamps_packed,
    );
    println!("DEBUG: it_host created, creating it_transfer");
    let mut it_transfer = InitsAndTeardownsTransfer::new(it_host, &context).unwrap();
    println!("DEBUG: it_transfer created");
    println!("DEBUG: scheduling it h2d");
    let it_h2d = crate::prover::transfer::single_shot_h2d(
        |t| it_transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    println!("DEBUG: waiting it h2d");
    it_h2d.ensure_transferred(&context).unwrap();
    println!("DEBUG: it h2d done, transferring setup");

    // Transfer GPU setup.
    let _setup_h2d = crate::prover::transfer::single_shot_h2d(
        |t| gpu_setup_transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();
    println!("DEBUG: setup transfer done, running stage1");

    // Run GPU stage1 with the Unified arm.
    let mut stage1_output = generate_stage1_output_for_test(
        CircuitType::Unrolled(UnrolledCircuitType::Unified),
        &compiled_circuit,
        &gpu_setup_transfer,
        if compiled_circuit.has_decoder_lookup {
            Some(&d_decoder_table)
        } else {
            None
        },
        Some(&it_transfer.data_device),
        &gpu_trace,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    println!("DEBUG: stage1 done, committing memory trace");

    // Stage1 does not commit memory traces in production; materialize here for
    // the hypercube readback (mirrors stagewise.rs:328-332).
    stage1_output
        .memory_trace_holder
        .commit_all(&context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    // Assert GPU memory columns == CPU full_trace over the FULL memory_layout.total_width.
    // This includes the inline inits/teardowns teardown columns (memory_layout.teardown_sets,
    // base cols ~30-33 in the unified layout) — the gate's intended regression coverage.
    // Read back one column at a time to avoid a single host-pool allocation for the
    // full trace (38 × 2^24 × 4 = 2.5 GB), which exceeds the default pinned host pool.
    {
        let gpu_hypercube = stage1_output.memory_trace_holder.get_hypercube_evals();
        for col in 0..compiled_circuit.memory_layout.total_width {
            let gpu_col_dev = &gpu_hypercube[col * trace_len..(col + 1) * trace_len];
            let gpu_col = copy_device_slice_to_host(gpu_col_dev, &context);
            let cpu_col = &full_trace.column_major_memory_trace[col];
            assert_eq!(
                &gpu_col[..],
                &cpu_col[..],
                "unified memory column {col} diverged"
            );
        }
    }

    // Assert GPU witness columns == CPU full_trace.
    {
        let gpu_hypercube = stage1_output.witness_trace_holder.get_hypercube_evals();
        for col in 0..compiled_circuit.witness_layout.total_width {
            let gpu_col_dev = &gpu_hypercube[col * trace_len..(col + 1) * trace_len];
            let gpu_col = copy_device_slice_to_host(gpu_col_dev, &context);
            let cpu_col = &full_trace.column_major_witness_trace[col];
            assert_eq!(
                &gpu_col[..],
                &cpu_col[..],
                "unified witness column {col} diverged"
            );
        }
    }

    println!(
        "GATE 1 PASS: unified witness ({} cols) + memory ({} cols, incl {} teardown sets) == CPU",
        compiled_circuit.witness_layout.total_width,
        compiled_circuit.memory_layout.total_width,
        num_unified_teardown_sets,
    );

    // -------------------------------------------------------------------------
    // GATE 2: GKR forward + backward parity (GPU == CPU stage-by-stage).
    // Mirrors stagewise.rs:382-775 with add_sub_circuit -> compiled_circuit and
    // unified-specific divergences described below.
    // -------------------------------------------------------------------------

    // external_challenges (same hard-coded values as the fixtures helpers).
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

    // Canonical top-bits for the unified circuit (teardown-set indices).
    let canonical_top_bits =
        crate::prover::proof::canonical_inits_and_teardowns_top_bits(&compiled_circuit);

    // Build transcript seed from GPU-committed caps (same ordering as proof/tests.rs:
    // canonical_top_bits, external_challenges, setup caps, memory caps, witness caps).
    let seed = {
        let setup_caps = gpu_setup_transfer
            .trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap();
        let memory_caps = stage1_output
            .memory_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap();
        let witness_caps = stage1_output
            .witness_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap();

        let mut transcript_input: Vec<u32> = Vec::new();
        transcript_input.extend_from_slice(&canonical_top_bits);
        external_challenges.flatten_into_buffer(&mut transcript_input);
        // setup caps
        for cap in setup_caps.iter() {
            for digest in cap.cap.iter() {
                transcript_input.extend_from_slice(digest);
            }
        }
        // memory caps
        for cap in memory_caps.iter() {
            for digest in cap.cap.iter() {
                transcript_input.extend_from_slice(digest);
            }
        }
        // witness caps
        for cap in witness_caps.iter() {
            for digest in cap.cap.iter() {
                transcript_input.extend_from_slice(digest);
            }
        }
        Transcript::commit_initial(&transcript_input)
    };

    // Draw lookup challenges from the seed.
    let mut seed = seed;
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();

    // --- Step 1+2: CPU forward GKR + GPU forward pass ---

    // Upload lookup challenges for schedule_forward_setup.
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
                &compiled_circuit,
                upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
                &context,
            )
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        gpu_forward_setup
    };

    // CPU forward: build GKR storage and run evaluate_layer for each layer.
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

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &compiled_circuit,
            &external_challenges,
            &mut witness_eval_data,
            &canonical_top_bits,
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

    // GPU forward pass + transcript handoff.
    let (gpu_forward_output, gpu_transcript_handoff) = {
        let _range = scoped_range(None, "test.gpu.forward.schedule");
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
    {
        let _range = scoped_range(None, "test.gpu.forward.readback_asserts");
        // The unified circuit DOES have generic lookup, range-check-16, and timestamp
        // mappings — the negated assertions from the add_sub sibling do NOT apply here.
        assert_eq!(
            gpu_forward_output.initial_layer_for_sumcheck,
            initial_layer_for_sumcheck
        );
        // Forward i/t-layer parity check: dimension_reducing_inputs includes the
        // OutputType::InitsAndTeardownsProduct entry (Task 9 forward arm).
        assert_eq!(
            gpu_forward_output.dimension_reducing_inputs,
            dimension_reducing_inputs
        );
        assert_eq!(gpu_final_explicit_evaluations, final_explicit_evaluations);
        assert_eq!(gpu_evals_flattened, evals_flattened);
    }
    drop(gpu_forward_setup);

    // --- Step 3: CPU transcript draw + initial claims ---

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
    // Unified-specific: insert the 2 i/t claims after the 8 from the helper
    // (10 total, not 8). The InitsAndTeardownsProduct entry is only present in
    // the unified circuit (Task 9 forward arm); a missing claim here would panic
    // in the backward claim_idx lookup (Task 11's fix is what makes the layout
    // carry them).
    {
        let it_io = &output_map[&OutputType::InitsAndTeardownsProduct];
        let eq_precomputed = make_eq_poly_in_full::<E4>(&evaluation_point, &worker);
        let eq = eq_precomputed.last().unwrap();
        let it_claim_0 =
            evaluate_ext_poly_with_eq(gkr_storage.get_ext_poly(it_io.output[0]), &eq[..]);
        let it_claim_1 =
            evaluate_ext_poly_with_eq(gkr_storage.get_ext_poly(it_io.output[1]), &eq[..]);
        top_layer_claims.insert(it_io.output[0], it_claim_0);
        top_layer_claims.insert(it_io.output[1], it_claim_1);
    }

    // --- Step 4: CPU backward sumcheck loop ---

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

    // Compute the address high bits shift for the unified circuit (matches
    // prover/src/gkr/prover/mod.rs logic: non-zero when top_bits are present).
    let address_high_bits_shift = if !canonical_top_bits.is_empty() {
        high_bits_offset_for_inits_and_teardowns::<2>(trace_len)
    } else {
        0u32
    };

    {
        let _range = scoped_range(None, "test.cpu.sumcheck.main_layers");
        for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate().rev() {
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
                &compiled_circuit,
                trace_len,
                lookup_alpha,
                lookup_additive_part,
                &canonical_top_bits,
                address_high_bits_shift,
                &external_challenges,
                &mut seed,
                &worker,
            );
            sumcheck_intermediate_values.insert(layer_idx, proof);
        }
    }

    // --- Step 5: GPU backward workflow + parity asserts ---

    // Build a real proof layout so the backward scheduler can write per-layer
    // sumcheck coefficients and final-step evaluations into the slab.
    let memory_geometry = crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
        GpuGKRTraceGeometry {
            log_domain_size: stage1_output.memory_trace_holder.log_domain_size,
            log_lde_factor: stage1_output.memory_trace_holder.log_lde_factor,
            log_rows_per_leaf: stage1_output.memory_trace_holder.log_rows_per_leaf,
            log_tree_cap_size: stage1_output.memory_trace_holder.log_tree_cap_size,
        },
        stage1_output.memory_trace_holder.columns_count,
    );
    let witness_geometry = crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
        GpuGKRTraceGeometry {
            log_domain_size: stage1_output.witness_trace_holder.log_domain_size,
            log_lde_factor: stage1_output.witness_trace_holder.log_lde_factor,
            log_rows_per_leaf: stage1_output.witness_trace_holder.log_rows_per_leaf,
            log_tree_cap_size: stage1_output.witness_trace_holder.log_tree_cap_size,
        },
        stage1_output.witness_trace_holder.columns_count,
    );
    let setup_geometry_dims =
        crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
            GpuGKRTraceGeometry {
                log_domain_size: gpu_setup_transfer.trace_holder.log_domain_size,
                log_lde_factor: gpu_setup_transfer.trace_holder.log_lde_factor,
                log_rows_per_leaf: gpu_setup_transfer.trace_holder.log_rows_per_leaf,
                log_tree_cap_size: gpu_setup_transfer.trace_holder.log_tree_cap_size,
            },
            gpu_setup_transfer.trace_holder.columns_count,
        );
    let proof_layout_inputs = crate::prover::proof::layout::build_proof_layout_inputs::<E4>(
        &compiled_circuit,
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
                compiled_circuit.clone(),
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

    println!(
        "GATE 2 PASS: GKR fwd+bwd ({} layers, {} dim-reducing) == CPU (10-claim top-layer incl i/t)",
        compiled_circuit.layers.len(),
        compiled_circuit.layers.len(), // dim-reducing count same as layer count for logging
    );
}
