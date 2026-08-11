use super::*;

/// Bucket sparse `(addr, (timestamp, value))` triples (per CPU-worker chunks) into the
/// page-based SoA wire format consumed by the GPU inits-and-teardowns kernel.
pub(super) fn build_inits_and_teardowns_pages_for_test(
    sparse: &[Vec<(u32, (common_constants::TimestampScalar, u32))>],
    trace_len_log2: u32,
    num_sets: u32,
) -> (Vec<u32>, Vec<u32>, Vec<common_constants::TimestampScalar>) {
    let selected_set_top_bits = (0..num_sets).collect::<Vec<_>>();
    build_inits_and_teardowns_pages_for_selected_sets_for_test(
        sparse,
        trace_len_log2,
        &selected_set_top_bits,
    )
}

pub(super) fn build_inits_and_teardowns_pages_for_selected_sets_for_test(
    sparse: &[Vec<(u32, (common_constants::TimestampScalar, u32))>],
    trace_len_log2: u32,
    selected_set_top_bits: &[u32],
) -> (Vec<u32>, Vec<u32>, Vec<common_constants::TimestampScalar>) {
    use std::collections::BTreeMap;

    assert!(PAGE_SIZE_LOG2 < trace_len_log2);
    let page_size = 1usize << PAGE_SIZE_LOG2;
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let pages_per_set_mask = (1u32 << pages_per_set_log2) - 1;

    let mut pages: BTreeMap<u32, (Vec<u32>, Vec<common_constants::TimestampScalar>)> =
        BTreeMap::new();
    for chunk in sparse {
        for &(address, (timestamp, value)) in chunk {
            let word_idx = address >> 2;
            let global_page_idx = word_idx >> PAGE_SIZE_LOG2;
            let global_set_top_bits = global_page_idx >> pages_per_set_log2;
            let local_set_idx = selected_set_top_bits
                .iter()
                .position(|&top_bits| top_bits == global_set_top_bits)
                .unwrap_or_else(|| {
                    panic!(
                        "test producer emitted page_idx {global_page_idx} from global set {global_set_top_bits}, which is absent from selected set top bits {selected_set_top_bits:?}",
                    )
                }) as u32;
            let page_idx =
                (local_set_idx << pages_per_set_log2) | (global_page_idx & pages_per_set_mask);
            let word_in_page = (word_idx & ((1u32 << PAGE_SIZE_LOG2) - 1)) as usize;
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

#[test]
fn cpu_selected_noncontiguous_sets_are_rebased_into_local_page_geometry() {
    let trace_len_log2 = PAGE_SIZE_LOG2 + 2;
    let selected_set_top_bits = [0, 2];
    let global_page_in_selected_set = 3u32;
    let word_in_page = 7u32;
    let global_word_idx = (selected_set_top_bits[1] << trace_len_log2)
        | (global_page_in_selected_set << PAGE_SIZE_LOG2)
        | word_in_page;
    let timestamp = 11;
    let value = 13;
    let sparse = vec![vec![(global_word_idx << 2, (timestamp, value))]];

    let (page_indices, values_packed, timestamps_packed) =
        build_inits_and_teardowns_pages_for_selected_sets_for_test(
            &sparse,
            trace_len_log2,
            &selected_set_top_bits,
        );

    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let expected_local_page = (1 << pages_per_set_log2) | global_page_in_selected_set;
    assert_eq!(page_indices, [expected_local_page]);
    assert_eq!(values_packed[word_in_page as usize], value);
    assert_eq!(timestamps_packed[word_in_page as usize], timestamp);
}

pub(super) fn build_inits_and_teardowns_trace_host_for_test(
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
pub(super) fn alloc_pinned_vec_from_slice_for_test<T: Copy>(
    values: &[T],
) -> Vec<T, gpu_core::allocator::host::ConcurrentStaticHostAllocator> {
    use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
    use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
    let bytes = std::mem::size_of_val(values);
    let allocation = HostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT).unwrap();
    let allocator = ConcurrentStaticHostAllocator::new([allocation], 0);
    let mut out: Vec<T, _> = Vec::with_capacity_in(values.len(), allocator);
    out.extend_from_slice(values);
    out
}

/// Build a `BasicUnrolledFixture` for the standalone inits-and-teardowns
/// circuit so it can be driven through the shared proof-matrix bodies
/// (`run_proof_parity` / `run_multi_schedule` / `run_profile`).
///
/// Structurally distinct from the per-family builders in two ways:
///   * The i/t witness is not per-cycle opcode replay — it is the RAM
///     init/teardown columns collected from the *same* VM run
///     (`collect_inits_and_teardowns_into_columns`), fed through
///     `evaluate_init_and_teardown_memory_witness` for the CPU reference and
///     `build_inits_and_teardowns_trace_host_for_test` for the GPU side.
///   * The preprocessed i/t layout has a zero-width setup
///     (`witness_layout.total_width == 0`), so `gpu_setup_host` is `None` and
///     the tracing-data host is an empty non-memory holder — the GPU prove()
///     drives the synthetic zero-width setup path.
///
/// Uses `hashed_fibonacci`, which produces non-empty RAM touches. When
/// `compute_cpu_reference` is false the
/// memory caps are derived from a lightweight CPU stage1 pass instead of a
/// full CPU proof (matches the profiling-fixture contract of the other
/// circuits).
pub(super) fn prepare_inits_and_teardowns_proof_fixture(
    compute_cpu_reference: bool,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: u32 = UnrolledCircuitType::InitsAndTeardowns.get_domain_size_log2();
    const FINAL_TRACE_SIZE_LOG_2: u32 = 4;

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

    // --- collect i/t from the same RAM: sparse triples (GPU pages) + per-set columns (CPU witness) ---
    let sparse_inits_and_teardowns = ram.collect_inits_and_teardowns(&worker, Global);
    let total_unique_teardowns: usize = sparse_inits_and_teardowns.iter().map(Vec::len).sum();
    assert_ne!(
        total_unique_teardowns, 0,
        "expected hashed-fibonacci RAM touches for standalone init/teardown fixture"
    );
    let compiled_circuit: GKRCircuitArtifact<BF> =
        deserialize_json_for_test("cs/compiled_circuits/inits_and_teardowns_layout_gkr.json");
    let num_sets = compiled_circuit.memory_layout.teardown_sets.len();
    let (page_indices, values_packed, timestamps_packed) = build_inits_and_teardowns_pages_for_test(
        &sparse_inits_and_teardowns,
        TRACE_LEN_LOG2,
        num_sets as u32,
    );
    let mut it_columns = Vec::with_capacity(num_sets);
    for _ in 0..num_sets {
        it_columns.push((
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
        TRACE_LEN_LOG2 as usize,
        0,
        &mut it_columns,
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
    let canonical_top_bits: Vec<u32> = (0..num_sets as u32).collect();

    let prover_config = crate::config::prover_config(
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        SecurityLevel::Sec80,
    )
    .unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();

    // --- CPU memory witness (memory-only trace) ---
    let cpu_memory_columns =
        evaluate_init_and_teardown_memory_witness(it_columns, &compiled_circuit, Global, Global);
    let make_full_trace = || GKRFullWitnessTrace {
        column_major_memory_trace: cpu_memory_columns.clone(),
        column_major_witness_trace: Vec::new(),
        column_major_scratch_space_trace: Vec::new(),
        generic_lookup_mapping: Vec::new(),
        range_check_16_lookup_mapping: Vec::new(),
        timestamp_range_check_lookup_mapping: Vec::new(),
    };

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let table_driver = TableDriver::<BF>::new();
    let setup = CpuGKRSetup::construct(&table_driver, &[], trace_len, &compiled_circuit);

    // --- CPU reference proof (only when requested) ---
    let expected_cpu_proof = if compute_cpu_reference {
        let setup_commitment = setup.commit(
            &twiddles,
            whir_schedule.base_lde_factor,
            whir_schedule.whir_steps_schedule[0],
            whir_schedule.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );
        Some(prove_configured_with_gkr::<
            BF,
            E4,
            DefaultTreeConstructor,
            Blake2sTranscript,
        >(
            &compiled_circuit,
            &external_challenges,
            make_full_trace(),
            &setup,
            &setup_commitment,
            &twiddles,
            &prover_config,
            CommitmentMode::SeparateMemoryAndWitness,
            canonical_top_bits.clone(),
            trace_len,
            &worker,
        ))
    } else {
        None
    };

    // --- memory tree caps fed to GPU prove(): from the CPU proof if present,
    //     else a lightweight CPU stage1 pass over the same memory trace ---
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
            .collect::<Vec<_>>()
    } else {
        let (mem_oracle, _wit_oracle) =
            commit_separate_memory_and_witness_subtrees::<BF, BF, DefaultTreeConstructor>(
                &NaiveBackend,
                &make_full_trace(),
                &twiddles,
                whir_schedule.base_lde_factor,
                whir_schedule.whir_steps_schedule[0],
                whir_schedule.cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );
        stage1_subcaps_from_cap(
            &mem_oracle.get_cap(),
            whir_schedule.cap_size / whir_schedule.base_lde_factor,
        )
    };

    // --- GPU-side hosts + context (matches the 64 GiB recycled-block arena the
    //     per-family fixtures use, so multi_schedule exercises the same path) ---
    let device_allocator_block_log_size = default_fixture_device_allocator_block_log_size();
    let device_allocator_arena_bytes: usize = 64usize << 30;
    let device_block_size = 1usize << device_allocator_block_log_size;
    let max_device_allocation_blocks_count = device_allocator_arena_bytes / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        1024,
        device_allocator_block_log_size,
    );

    let inits_and_teardowns_host = build_inits_and_teardowns_trace_host_for_test(
        &page_indices,
        &values_packed,
        &timestamps_packed,
    );
    // Standalone i/t proves no per-cycle witness: empty non-memory tracing host,
    // and no decoder lookup (the default guard keeps the pinned alloc non-empty).
    let tracing_data_host = make_non_memory_tracing_host_for_test(Vec::new());
    let decoder_table_host = make_decoder_table_host_for_test(&[]);
    debug_assert!(!compiled_circuit.has_decoder_lookup);

    (
        BasicUnrolledFixture {
            context,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            gkr_programs: Arc::new(
                GkrPrograms::compile(
                    CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                    Arc::new(compiled_circuit.clone()),
                )
                .expect("fixture must compile its committed GKR programs"),
            ),
            compiled_circuit,
            external_challenges,
            prover_config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host: None,
            decoder_table_host,
            tracing_data_host,
            memory_tree_caps,
            inits_and_teardowns_host: Some(inits_and_teardowns_host),
            inits_and_teardowns_top_bits: None,
            unified_register_final_state: [(0u32, (0u32, 0u32)); 32],
            unified_final_pc: 0,
            unified_final_timestamp: 0,
            delegation_grand_product_factors: Vec::new(),
        },
        expected_cpu_proof,
    )
}
