use super::*;

/// Bucket sparse `(addr, (timestamp, value))` triples (per CPU-worker chunks) into the
/// page-based SoA wire format consumed by the GPU inits-and-teardowns kernel.
fn build_inits_and_teardowns_pages_for_test(
    sparse: &[Vec<(u32, (common_constants::TimestampScalar, u32))>],
    trace_len_log2: u32,
    num_sets: u32,
) -> (Vec<u32>, Vec<u32>, Vec<common_constants::TimestampScalar>) {
    use std::collections::BTreeMap;

    assert!(PAGE_SIZE_LOG2 < trace_len_log2);
    let page_size = 1usize << PAGE_SIZE_LOG2;
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let max_page_idx = (num_sets as u64) << pages_per_set_log2;

    let mut pages: BTreeMap<u32, (Vec<u32>, Vec<common_constants::TimestampScalar>)> =
        BTreeMap::new();
    for chunk in sparse {
        for &(address, (timestamp, value)) in chunk {
            let word_idx = address >> 2;
            let page_idx = word_idx >> PAGE_SIZE_LOG2;
            let word_in_page = (word_idx & ((1u32 << PAGE_SIZE_LOG2) - 1)) as usize;
            assert!(
                (page_idx as u64) < max_page_idx,
                "test producer emitted page_idx {page_idx} that decodes to set_idx >= num_sets ({num_sets})",
            );
            let entry = pages
                .entry(page_idx)
                .or_insert_with(|| (vec![0u32; page_size], vec![0u64; page_size]));
            entry.0[word_in_page] = value;
            entry.1[word_in_page] = timestamp;
        }
    }

    let num_pages = pages.len();
    let mut page_indices = Vec::with_capacity(num_pages);
    let mut values_packed = Vec::with_capacity(num_pages * page_size);
    let mut timestamps_packed = Vec::with_capacity(num_pages * page_size);
    for (page_idx, (vals, tss)) in pages {
        page_indices.push(page_idx);
        values_packed.extend_from_slice(&vals);
        timestamps_packed.extend_from_slice(&tss);
    }
    (page_indices, values_packed, timestamps_packed)
}

fn build_inits_and_teardowns_trace_host_for_test(
    page_indices: &[u32],
    values_packed: &[u32],
    timestamps_packed: &[common_constants::TimestampScalar],
) -> InitsAndTeardownsTraceHost {
    InitsAndTeardownsTraceHost {
        page_indices: ChunkedTraceHolder {
            chunks: vec![Arc::new(alloc_pinned_vec_from_slice_for_test(page_indices))],
        },
        values_packed: ChunkedTraceHolder {
            chunks: vec![Arc::new(alloc_pinned_vec_from_slice_for_test(
                values_packed,
            ))],
        },
        timestamps_packed: ChunkedTraceHolder {
            chunks: vec![Arc::new(alloc_pinned_vec_from_slice_for_test(
                timestamps_packed,
            ))],
        },
    }
}

/// Build a single pinned-host `Vec<T, ConcurrentStaticHostAllocator>` from a slice.
///
/// Each call dedicates a private `ConcurrentStaticHostAllocator` that owns one fresh
/// `HostAllocation`, mirroring the per-chunk pinned allocation pattern used in the
/// production producer's pool allocators (single-chunk degenerate case).
fn alloc_pinned_vec_from_slice_for_test<T: Copy>(
    values: &[T],
) -> Vec<T, crate::allocator::host::ConcurrentStaticHostAllocator> {
    use crate::allocator::host::ConcurrentStaticHostAllocator;
    use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
    let bytes = values.len() * std::mem::size_of::<T>();
    let allocation = HostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT).unwrap();
    let allocator = ConcurrentStaticHostAllocator::new([allocation], 0);
    let mut out: Vec<T, _> = Vec::with_capacity_in(values.len(), allocator);
    out.extend_from_slice(values);
    out
}

#[test]
#[cfg(not(no_cuda))]
#[ignore]
#[serial]
fn standalone_inits_and_teardowns_gpu_workflow_matches_cpu() {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;

    let trace_len = 1usize << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let binary = read_test_words("examples/hashed_fibonacci/app.bin");
    let text_section = read_test_words("examples/hashed_fibonacci/app.text");
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
    assert!(is_program_finished);

    let sparse_inits_and_teardowns = ram.collect_inits_and_teardowns(&worker, Global);
    let total_unique_teardowns: usize = sparse_inits_and_teardowns.iter().map(Vec::len).sum();
    assert_ne!(
        total_unique_teardowns, 0,
        "expected hashed-fibonacci RAM touches for standalone init/teardown parity"
    );
    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(
        "cs/compiled_circuits/inits_and_teardowns_preprocessed_layout_gkr.json",
    );
    let num_init_and_teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
    let (page_indices, values_packed, timestamps_packed) = build_inits_and_teardowns_pages_for_test(
        &sparse_inits_and_teardowns,
        TRACE_LEN_LOG2 as u32,
        num_init_and_teardown_sets as u32,
    );
    let mut inits_and_teardowns_columns = Vec::with_capacity(num_init_and_teardown_sets);
    for _ in 0..num_init_and_teardown_sets {
        inits_and_teardowns_columns.push((
            [
                Vec::with_capacity(1 << TRACE_LEN_LOG2),
                Vec::with_capacity(1 << TRACE_LEN_LOG2),
            ],
            [
                Vec::with_capacity(1 << TRACE_LEN_LOG2),
                Vec::with_capacity(1 << TRACE_LEN_LOG2),
            ],
        ));
    }
    ram.collect_inits_and_teardowns_into_columns::<BF, _>(
        &worker,
        TRACE_LEN_LOG2,
        0,
        &mut inits_and_teardowns_columns,
    );

    assert_eq!(compiled_circuit.trace_len, trace_len);
    assert_eq!(compiled_circuit.witness_layout.total_width, 0);

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
    let external_challenges = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };
    let canonical_top_bits: Vec<_> =
        (0..compiled_circuit.memory_layout.teardown_sets.len() as u32).collect();

    let cpu_memory_columns = evaluate_init_and_teardown_memory_witness(
        inits_and_teardowns_columns.clone(),
        &compiled_circuit,
        Global,
        Global,
    );
    let cpu_full_trace_for_stagewise = GKRFullWitnessTrace {
        column_major_memory_trace: cpu_memory_columns.clone(),
        column_major_witness_trace: Vec::new(),
        column_major_scratch_space_trace: Vec::new(),
        generic_lookup_mapping: Vec::new(),
        range_check_16_lookup_mapping: Vec::new(),
        timestamp_range_check_lookup_mapping: Vec::new(),
    };
    let cpu_full_trace_for_proof = GKRFullWitnessTrace {
        column_major_memory_trace: cpu_memory_columns.clone(),
        column_major_witness_trace: Vec::new(),
        column_major_scratch_space_trace: Vec::new(),
        generic_lookup_mapping: Vec::new(),
        range_check_16_lookup_mapping: Vec::new(),
        timestamp_range_check_lookup_mapping: Vec::new(),
    };

    let table_driver = TableDriver::<BF>::new();
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let prover_config = crate::prover::config::prover_config(
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        SecurityLevel::Sec80,
    )
    .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(&table_driver, &[], trace_len, &compiled_circuit);
    assert!(setup.hypercube_evals.is_empty());
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
        cpu_full_trace_for_proof,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        canonical_top_bits.clone(),
        trace_len,
        &worker,
    );
    let (mem_oracle, _wit_oracle) = stage1::stage1::<BF, DefaultTreeConstructor>(
        &cpu_full_trace_for_stagewise,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let cpu_memory_caps = stage1_caps_from_tree(
        &mem_oracle.tree,
        whir_schedule.cap_size / whir_schedule.base_lde_factor,
    );

    let context = make_test_context(64 * 1024, 1024);
    {
        let tracing_data_host = make_non_memory_tracing_host_for_test(Vec::new());
        let mut tracing_data_transfer =
            TracingDataTransfer::new(tracing_data_host, &context).unwrap();
        let inits_and_teardowns_host = build_inits_and_teardowns_trace_host_for_test(
            &page_indices,
            &values_packed,
            &timestamps_packed,
        );
        let mut inits_and_teardowns_transfer =
            InitsAndTeardownsTransfer::new(inits_and_teardowns_host, &context).unwrap();
        let transfer = crate::prover::transfer::single_shot_h2d(
            |t| {
                tracing_data_transfer.schedule_transfer(t, &context)?;
                inits_and_teardowns_transfer.schedule_transfer(t, &context)
            },
            &context,
        )
        .unwrap();
        transfer.ensure_transferred(&context).unwrap();

        let geometry = GpuGKRTraceGeometry {
            log_domain_size: trace_len.trailing_zeros(),
            log_lde_factor: whir_schedule.base_lde_factor.trailing_zeros(),
            log_rows_per_leaf: whir_schedule.whir_steps_schedule[0] as u32,
            log_tree_cap_size: whir_schedule.cap_size.trailing_zeros(),
        };
        let mut stage1_output = GpuGKRStage1Output::generate(
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            &compiled_circuit,
            geometry,
            None,
            None,
            Some(&inits_and_teardowns_transfer.data_device),
            Some(&tracing_data_transfer.data_device),
            None,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        stage1_output
            .memory_trace_holder
            .commit_all(&context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        if let Some(mismatch) = describe_first_trace_holder_column_mismatch(
            &stage1_output.memory_trace_holder,
            &cpu_memory_columns,
            trace_len,
            &context,
        ) {
            panic!("standalone init/teardown stage1 memory trace mismatch: {mismatch}");
        }
        assert_eq!(
            stage1_output
                .memory_trace_holder
                .read_per_coset_caps_synchronously(&context)
                .unwrap(),
            cpu_memory_caps,
            "standalone init/teardown memory caps diverged"
        );

        let mut cpu_transcript_input = Vec::new();
        cpu_transcript_input.extend_from_slice(&canonical_top_bits);
        external_challenges.flatten_into_buffer(&mut cpu_transcript_input);
        flatten_merkle_caps_iter_into(
            Some(
                <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                    &mem_oracle.tree,
                ),
            )
            .into_iter(),
            &mut cpu_transcript_input,
        );
        let mut cpu_seed = Transcript::commit_initial(&cpu_transcript_input);
        let cpu_lookup_challenges: [E4; 3] = draw_random_field_els::<BF, E4>(&mut cpu_seed, 3)
            .try_into()
            .unwrap();

        let mut gpu_transcript_input = Vec::new();
        gpu_transcript_input.extend_from_slice(&canonical_top_bits);
        external_challenges.flatten_into_buffer(&mut gpu_transcript_input);
        for cap in stage1_output
            .memory_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
            .iter()
        {
            for digest in cap.cap.iter() {
                gpu_transcript_input.extend_from_slice(digest);
            }
        }
        let mut gpu_seed = Transcript::commit_initial(&gpu_transcript_input);
        let gpu_lookup_challenges: [E4; 3] = draw_random_field_els::<BF, E4>(&mut gpu_seed, 3)
            .try_into()
            .unwrap();
        assert_eq!(
            gpu_seed, cpu_seed,
            "transcript seed initialization diverged"
        );
        assert_eq!(
            gpu_lookup_challenges, cpu_lookup_challenges,
            "transcript-derived lookup challenges diverged"
        );

        // `evaluate_layer` no longer takes the constraints-batch challenge; ignore the third
        // element so the destructuring still mirrors the on-device 3-tuple layout.
        let [lookup_alpha, lookup_additive_part, _constraints_batch_challenge] =
            cpu_lookup_challenges;
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
        let mut witness_eval_data = GKRFullWitnessTrace {
            column_major_memory_trace: cpu_memory_columns.clone(),
            column_major_witness_trace: Vec::new(),
            column_major_scratch_space_trace: Vec::new(),
            generic_lookup_mapping: Vec::new(),
            range_check_16_lookup_mapping: Vec::new(),
            timestamp_range_check_lookup_mapping: Vec::new(),
        };
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
        let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
            dimension_reduction::forward::evaluate_dimension_reduction_forward(
                &mut gkr_storage,
                &compiled_circuit,
                trace_len.trailing_zeros() as usize,
                FINAL_TRACE_SIZE_LOG_2,
                &worker,
            );
        let output_layer_for_sumcheck = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
        let (final_explicit_evaluations, evals_flattened) =
            collect_final_explicit_evaluations_for_test(
                &gkr_storage,
                output_layer_for_sumcheck,
                1 << FINAL_TRACE_SIZE_LOG_2,
            );

        let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
        unsafe {
            lookup_challenges_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&cpu_lookup_challenges);
        }
        let mut gpu_forward_setup =
            crate::prover::gkr::setup::schedule_forward_setup_for_shape::<E4>(
                None,
                compiled_circuit.trace_len,
                compiled_circuit.generic_lookup_tables_width,
                compiled_circuit.total_tables_size,
                compiled_circuit.tables_ids_in_generic_lookups,
                upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
                &context,
            )
            .unwrap();
        let synthetic_setup_trace_holder = TraceHolder::new_without_cosets(
            geometry.log_domain_size,
            geometry.log_lde_factor,
            geometry.log_rows_per_leaf,
            geometry.log_tree_cap_size,
            0,
            crate::prover::trace::holder::TreesCacheMode::CachePartial,
            &context,
        )
        .unwrap();
        let gpu_forward_output = schedule_forward_pass_impl(
            None,
            Some(&synthetic_setup_trace_holder),
            &mut stage1_output,
            &mut gpu_forward_setup,
            &compiled_circuit,
            &external_challenges,
            FINAL_TRACE_SIZE_LOG_2,
            None,
            &context,
        )
        .unwrap();
        let gpu_transcript_handoff = gpu_forward_output
            .schedule_transcript_handoff(true, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        assert_eq!(
            gpu_forward_output.initial_layer_for_sumcheck,
            initial_layer_for_sumcheck
        );
        assert_eq!(
            gpu_forward_output.dimension_reducing_inputs,
            dimension_reducing_inputs
        );
        assert_eq!(
            gpu_transcript_handoff.final_explicit_evaluations(),
            final_explicit_evaluations
        );
        assert_eq!(
            gpu_transcript_handoff.flattened_transcript_evaluations(),
            evals_flattened
        );
    }

    let inits_and_teardowns_host = build_inits_and_teardowns_trace_host_for_test(
        &page_indices,
        &values_packed,
        &timestamps_packed,
    );
    let tracing_data_host = make_non_memory_tracing_host_for_test(Vec::new());
    let inits_and_teardowns_transfer =
        InitsAndTeardownsTransfer::new(inits_and_teardowns_host, &context).unwrap();
    let tracing_data_transfer = TracingDataTransfer::new(tracing_data_host, &context).unwrap();
    let memory_transfer_host = Arc::new(
        crate::prover::trace::memory_transfer::GpuGKRMemoryTransferHost::from_per_coset_caps(
            &cpu_memory_caps,
            whir_schedule.base_lde_factor.trailing_zeros(),
            whir_schedule.cap_size.trailing_zeros(),
        )
        .unwrap(),
    );
    let memory_transfer = crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer::new(
        memory_transfer_host,
        &context,
    )
    .unwrap();
    let canonical_top_bits =
        crate::prover::proof::canonical_inits_and_teardowns_top_bits(&compiled_circuit);
    let mut bundle = crate::prover::proof::inputs::GpuGKRProofTransfer::<'_, Global>::new(
        None,
        None,
        Some(inits_and_teardowns_transfer),
        Some(tracing_data_transfer),
        memory_transfer,
        &canonical_top_bits,
        external_challenges,
        &context,
    )
    .unwrap();
    bundle.schedule(&context).unwrap();
    let gpu_job = prove::<Global>(
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        compiled_circuit.clone(),
        &prover_config,
        FINAL_TRACE_SIZE_LOG_2,
        bundle,
        &context,
    )
    .unwrap();
    let (gpu_proof, _) = gpu_job.finish().unwrap();

    assert_eq!(
        gpu_proof.final_explicit_evaluations,
        expected_cpu_proof.final_explicit_evaluations
    );
    assert_eq!(
        gpu_proof.grand_product_accumulator_computed,
        expected_cpu_proof.grand_product_accumulator_computed
    );
    if total_unique_teardowns == 0 {
        assert_eq!(gpu_proof.grand_product_accumulator_computed, E4::ONE);
        assert_eq!(
            expected_cpu_proof.grand_product_accumulator_computed,
            E4::ONE
        );
    }
}

#[test]
fn standalone_inits_and_teardowns_trivial_accumulator_matches_cpu_expectation() {
    let final_explicit_evaluations = BTreeMap::from([
        (
            OutputType::PermutationProduct,
            [vec![E4::ONE; 4], vec![E4::ONE; 4]],
        ),
        (
            OutputType::Lookup16Bits,
            [vec![E4::ONE; 4], vec![E4::ONE; 4]],
        ),
        (
            OutputType::LookupTimestamps,
            [vec![E4::ONE; 4], vec![E4::ONE; 4]],
        ),
        (
            OutputType::GenericLookup,
            [vec![E4::ONE; 4], vec![E4::ONE; 4]],
        ),
    ]);

    assert_eq!(
        grand_product_accumulator_from_explicit_evaluations(&final_explicit_evaluations),
        E4::ONE
    );
}
