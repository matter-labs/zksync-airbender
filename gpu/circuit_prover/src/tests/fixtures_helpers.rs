use super::*;

const DEFAULT_FIXTURE_DEVICE_ARENA_BYTES: usize = 64usize << 30;
const NCU_PROFILE_DEVICE_ARENA_BYTES: usize = 32usize << 30;

pub(super) fn default_fixture_device_allocator_block_log_size() -> u32 {
    gpu_prover_context::ProverContextConfig::default().allocator_block_log_size
}

/// Data extracted from a binary/text run for a single executor family.
pub(super) struct ExtractedFamily {
    /// Replay buffer for the non-memory opcodes that were traced.
    /// `Some` for non-memory families.
    pub buffer_non_memory: Option<Vec<NonMemoryOpcodeTracingDataWithTimestamp>>,
    /// Replay buffer for memory opcodes. `Some` for memory-circuit families.
    pub buffer_memory: Option<Vec<MemoryOpcodeTracingDataWithTimestamp>>,
    /// Per-PC decoder entries for the family (one `Option` per bytecode word).
    pub decoder_table_data: Vec<Option<CSExecutorFamilyDecoderData>, Global>,
    /// Flattened witness-gen data derived from `decoder_table_data`.
    pub witness_gen_data: Vec<CSExecutorFamilyDecoderData>,
    /// Parsed binary words — needed by memory-circuit families to build
    /// binary-derived special tables via `build_table_driver`.
    pub binary: Vec<u32>,
}

/// Front end: run the VM, replay, and extract the family-specific tables.
///
/// Const-generic on `FAMILY_IDX` so the `NonMemDestinationHolder` and
/// `counters.get_calls_to_circuit_family` calls are monomorphized correctly.
pub(super) fn extract_non_memory_family<const FAMILY_IDX: u8>(
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: &[u32],
) -> ExtractedFamily {
    type CountersT = DelegationsAndFamiliesCounters;

    let cycles_bound = 1 << 20;

    let binary = std::fs::read(test_artifact_path(binary_path)).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section = std::fs::read(test_artifact_path(text_path)).unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);

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

    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<FAMILY_IDX> {
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
    drop(snapshotter);
    drop(ram);
    drop(non_determinism);
    drop(tape);
    drop(instructions);
    drop(text_section);

    let decoder_table_data = preprocessing_data
        .remove(&FAMILY_IDX)
        .expect("fixture must contain preprocessed data for the requested family");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    drop(preprocessing_data);

    ExtractedFamily {
        buffer_non_memory: Some(buffer),
        buffer_memory: None,
        decoder_table_data,
        witness_gen_data,
        binary,
    }
}

/// Tail: builds the full `BasicUnrolledFixture` (and optional CPU reference proof)
/// from already-extracted family data.
///
/// The oracle borrow is managed internally: the `buffer` is used to construct a
/// `NonMemoryCircuitOracle` for the optional CPU proof, then consumed by
/// `make_non_memory_tracing_host_for_test` afterwards.
///
/// Both `CpuGKRSetup::construct` and `evaluate_gkr_witness_for_executor_family`
/// use the caller-supplied `table_driver` (the family's real driver, NOT a blank
/// `TableDriver::new()`).
pub(super) fn finish_proof_fixture(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    buffer: Vec<NonMemoryOpcodeTracingDataWithTimestamp>,
    default_pc_value_in_padding: u32,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            NonMemoryCircuitOracle<'_>,
            BF,
        >,
    ),
    table_driver: &TableDriver<BF>,
    decoder_table_data: &[Option<CSExecutorFamilyDecoderData>],
    witness_gen_data: &[CSExecutorFamilyDecoderData],
    compute_cpu_reference: bool,
    device_allocator_block_log_size: u32,
    device_allocator_arena_bytes: usize,
    security_level: SecurityLevel,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    const FINAL_TRACE_SIZE_LOG_2: u32 = 4;
    const HOST_POOL_SIZE_MB: usize = 1024;
    let trace_len: usize = compiled_circuit.trace_len;

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

    let fixture_circuit_type = circuit_type;
    let prover_config = crate::config::prover_config(fixture_circuit_type, security_level).unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(
        table_driver,
        decoder_table_data,
        trace_len,
        &compiled_circuit,
    );
    assert!(
        device_allocator_block_log_size >= 4,
        "basic unrolled fixture requires a device allocator block log size of at least 4 for aligned GPU allocations, got {}",
        device_allocator_block_log_size,
    );
    let device_block_size = 1usize << device_allocator_block_log_size;
    let max_device_allocation_blocks_count = device_allocator_arena_bytes / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        device_allocator_block_log_size,
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
    let decoder_table_host = make_decoder_table_host_for_test(witness_gen_data);
    eprintln!("fixture: decoder host ready");

    let expected_cpu_proof = if compute_cpu_reference {
        let worker = Worker::new_with_num_threads(8);
        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: decoder_table_data,
            default_pc_value_in_padding,
        };

        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            trace_len,
            &oracle,
            &worker,
            None,
            Global,
            Global,
        );
        let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            witness_eval_fn,
            trace_len,
            &oracle,
            table_driver,
            &worker,
            None,
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
        let expected_cpu_proof =
            prove_configured_with_gkr::<BF, E4, DefaultTreeConstructor, Blake2sTranscript>(
                &compiled_circuit,
                &external_challenges,
                full_trace,
                &setup,
                &setup_commitment,
                &twiddles,
                &prover_config,
                CommitmentMode::SeparateMemoryAndWitness,
                vec![],
                trace_len,
                &worker,
            );
        eprintln!("fixture: cpu proof ready");
        Some(expected_cpu_proof)
    } else {
        None
    };

    // `buffer` is consumed here; the oracle above (if any) has already been
    // dropped since it only borrows for the `compute_cpu_reference` block.
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

        // One-shot Transfer: schedule every H2D against it, record_transferred,
        // ensure_transferred, then run `commit_memory` against the now-visible
        // device buffers.
        let transfer = gpu_prover_context::transfer::single_shot_h2d(
            |t| {
                setup_transfer.schedule_transfer(t, &context)?;
                if let Some(decoder_transfer) = decoder_transfer.as_mut() {
                    decoder_transfer.schedule_transfer(t, &context)?;
                }
                tracing_data_transfer.schedule_transfer(t, &context)?;
                Ok(())
            },
            &context,
        )
        .unwrap();
        transfer.ensure_transferred(&context).unwrap();

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
        drop(transfer);
        drop(setup_transfer);
        drop(decoder_transfer);
        drop(tracing_data_transfer);
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
            gkr_programs: Arc::new(
                GkrPrograms::compile(fixture_circuit_type, Arc::new(compiled_circuit.clone()))
                    .expect("fixture must compile its committed GKR programs"),
            ),
            compiled_circuit,
            external_challenges,
            prover_config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host: Some(gpu_setup_host),
            decoder_table_host,
            tracing_data_host,
            memory_tree_caps,
            // Per-family fixtures have no inits-and-teardowns layer and no
            // unified-closure metadata; the unified fixture populates these.
            inits_and_teardowns_host: None,
            inits_and_teardowns_top_bits: None,
            unified_register_final_state: [(0u32, (0u32, 0u32)); 32],
            unified_final_pc: 0,
            unified_final_timestamp: 0,
            delegation_grand_product_factors: Vec::new(),
        },
        expected_cpu_proof,
    )
}

/// Generic builder for any non-memory circuit family.
///
/// Binary/text paths are fixed to the shared keccak_f1600 workload
/// (`BASIC_UNROLLED_CPU_PARITY_*`). The const-generic `FAMILY_IDX` selects
/// the correct `NonMemDestinationHolder` / `counters.get_calls_to_circuit_family`
/// monomorphization inside `extract_non_memory_family`.
pub(super) fn prepare_unrolled_non_memory_proof_fixture<const FAMILY_IDX: u8>(
    non_determinism_reads: &[u32],
    default_pc_value_in_padding: u32,
    circuit_type: UnrolledNonMemoryCircuitType,
    layout_path: &str,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            NonMemoryCircuitOracle<'_>,
            BF,
        >,
    ),
    build_table_driver: impl FnOnce(&mut TableDriver<BF>),
    compute_cpu_reference: bool,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    let ex = extract_non_memory_family::<FAMILY_IDX>(
        BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
        BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
        non_determinism_reads,
    );
    let buffer = ex.buffer_non_memory.unwrap();
    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(layout_path);
    let mut table_driver = TableDriver::<BF>::new();
    build_table_driver(&mut table_driver);
    finish_proof_fixture(
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
        compiled_circuit,
        buffer,
        default_pc_value_in_padding,
        witness_eval_fn,
        &table_driver,
        &ex.decoder_table_data,
        &ex.witness_gen_data,
        compute_cpu_reference,
        default_fixture_device_allocator_block_log_size(),
        DEFAULT_FIXTURE_DEVICE_ARENA_BYTES,
        crate::upstream::SecurityLevel::Sec80,
    )
}

/// Extract-side analog of `extract_non_memory_family` for memory-circuit families.
///
/// Uses `MemDestinationHolder::<FAMILY_IDX>` as the tracer and produces a
/// `Vec<MemoryOpcodeTracingDataWithTimestamp>` buffer (returned in
/// `ExtractedFamily::buffer_memory`). The parsed `binary` is also surfaced so
/// callers can build binary-derived special tables.
pub(super) fn extract_memory_family<const FAMILY_IDX: u8>(
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: &[u32],
) -> ExtractedFamily {
    type CountersT = DelegationsAndFamiliesCounters;

    let cycles_bound = 1 << 20;

    let binary = std::fs::read(test_artifact_path(binary_path)).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section = std::fs::read(test_artifact_path(text_path)).unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);

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

    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    assert!(
        num_calls > 0,
        "selected workload must exercise memory family {FAMILY_IDX}",
    );
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![MemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
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
    drop(snapshotter);
    drop(ram);
    drop(non_determinism);
    drop(tape);
    drop(instructions);
    drop(text_section);

    let decoder_table_data = preprocessing_data
        .remove(&FAMILY_IDX)
        .expect("fixture must contain preprocessed data for the requested family");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    drop(preprocessing_data);

    ExtractedFamily {
        buffer_non_memory: None,
        buffer_memory: Some(buffer),
        decoder_table_data,
        witness_gen_data,
        binary,
    }
}

/// Tail: builds the full `BasicUnrolledFixture` (and optional CPU reference proof)
/// from already-extracted memory-family data.
///
/// Analog of `finish_proof_fixture` for memory circuits. The oracle is
/// `MemoryCircuitOracle { inner, decoder_table }` (no `default_pc_value_in_padding`
/// — memory oracles have no such field). The `build_table_driver` closure receives
/// the parsed binary so it can populate binary-derived special tables.
pub(super) fn finish_proof_fixture_memory(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    buffer: Vec<MemoryOpcodeTracingDataWithTimestamp>,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            MemoryCircuitOracle<'_>,
            BF,
        >,
    ),
    table_driver: &TableDriver<BF>,
    decoder_table_data: &[Option<CSExecutorFamilyDecoderData>],
    witness_gen_data: &[CSExecutorFamilyDecoderData],
    compute_cpu_reference: bool,
    device_allocator_block_log_size: u32,
    security_level: SecurityLevel,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    const FINAL_TRACE_SIZE_LOG_2: u32 = 4;
    const HOST_POOL_SIZE_MB: usize = 1024;
    let device_allocator_arena_bytes: usize = 64usize << 30;

    let trace_len: usize = compiled_circuit.trace_len;
    assert!(buffer.len() < trace_len);

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

    let fixture_circuit_type = circuit_type;
    let prover_config = crate::config::prover_config(fixture_circuit_type, security_level).unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();
    let setup = CpuGKRSetup::construct(
        table_driver,
        decoder_table_data,
        trace_len,
        &compiled_circuit,
    );
    assert!(
        device_allocator_block_log_size >= 4,
        "basic unrolled fixture requires a device allocator block log size of at least 4 for aligned GPU allocations, got {}",
        device_allocator_block_log_size,
    );
    let device_block_size = 1usize << device_allocator_block_log_size;
    let max_device_allocation_blocks_count = device_allocator_arena_bytes / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        device_allocator_block_log_size,
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
    let decoder_table_host = make_decoder_table_host_for_test(witness_gen_data);
    eprintln!("fixture(memory): decoder host ready");

    let expected_cpu_proof = if compute_cpu_reference {
        let worker = Worker::new_with_num_threads(8);
        let oracle = MemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: decoder_table_data,
        };

        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            trace_len,
            &oracle,
            &worker,
            None,
            Global,
            Global,
        );
        let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            witness_eval_fn,
            trace_len,
            &oracle,
            table_driver,
            &worker,
            None,
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
        let expected_cpu_proof =
            prove_configured_with_gkr::<BF, E4, DefaultTreeConstructor, Blake2sTranscript>(
                &compiled_circuit,
                &external_challenges,
                full_trace,
                &setup,
                &setup_commitment,
                &twiddles,
                &prover_config,
                CommitmentMode::SeparateMemoryAndWitness,
                vec![],
                trace_len,
                &worker,
            );
        eprintln!("fixture(memory): cpu proof ready");
        Some(expected_cpu_proof)
    } else {
        None
    };

    // `buffer` is consumed here; the oracle above (if any) has already been
    // dropped since it only borrows for the `compute_cpu_reference` block.
    let tracing_data_host = make_memory_tracing_host_for_test(buffer);
    eprintln!("fixture(memory): tracing host ready");

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

        let transfer = gpu_prover_context::transfer::single_shot_h2d(
            |t| {
                setup_transfer.schedule_transfer(t, &context)?;
                if let Some(decoder_transfer) = decoder_transfer.as_mut() {
                    decoder_transfer.schedule_transfer(t, &context)?;
                }
                tracing_data_transfer.schedule_transfer(t, &context)?;
                Ok(())
            },
            &context,
        )
        .unwrap();
        transfer.ensure_transferred(&context).unwrap();

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
        drop(transfer);
        drop(setup_transfer);
        drop(decoder_transfer);
        drop(tracing_data_transfer);
        tree_caps
    };

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
            gkr_programs: Arc::new(
                GkrPrograms::compile(fixture_circuit_type, Arc::new(compiled_circuit.clone()))
                    .expect("fixture must compile its committed GKR programs"),
            ),
            compiled_circuit,
            external_challenges,
            prover_config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host: Some(gpu_setup_host),
            decoder_table_host,
            tracing_data_host,
            memory_tree_caps,
            inits_and_teardowns_host: None,
            inits_and_teardowns_top_bits: None,
            unified_register_final_state: [(0u32, (0u32, 0u32)); 32],
            unified_final_pc: 0,
            unified_final_timestamp: 0,
            delegation_grand_product_factors: Vec::new(),
        },
        expected_cpu_proof,
    )
}

/// Generic builder for any memory circuit family.
///
/// Binary/text paths are fixed to the shared keccak_f1600 workload
/// (`BASIC_UNROLLED_CPU_PARITY_*`). The const-generic `FAMILY_IDX` selects
/// the correct `MemDestinationHolder` / `counters.get_calls_to_circuit_family`
/// monomorphization inside `extract_memory_family`.
///
/// The layout is deserialized from JSON rather than compiled per-test — the
/// layout is binary-independent; only the driver's special tables are
/// binary-derived (passed via `build_table_driver(&mut td, &binary)`).
pub(super) fn prepare_unrolled_memory_proof_fixture<const FAMILY_IDX: u8>(
    non_determinism_reads: &[u32],
    circuit_type: UnrolledMemoryCircuitType,
    layout_path: &str,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            MemoryCircuitOracle<'_>,
            BF,
        >,
    ),
    build_table_driver: impl FnOnce(&mut TableDriver<BF>, &[u32]),
    compute_cpu_reference: bool,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    let ex = extract_memory_family::<FAMILY_IDX>(
        BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
        BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
        non_determinism_reads,
    );
    let buffer = ex.buffer_memory.unwrap();
    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(layout_path);
    let mut table_driver = TableDriver::<BF>::new();
    build_table_driver(&mut table_driver, &ex.binary);
    finish_proof_fixture_memory(
        CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type)),
        compiled_circuit,
        buffer,
        witness_eval_fn,
        &table_driver,
        &ex.decoder_table_data,
        &ex.witness_gen_data,
        compute_cpu_reference,
        default_fixture_device_allocator_block_log_size(),
        crate::upstream::SecurityLevel::Sec80,
    )
}

pub(super) fn prepare_basic_unrolled_fixture(
    build_config: BasicUnrolledFixtureBuildConfig<'_>,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    let ex = extract_non_memory_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
        build_config.binary_path,
        build_config.text_path,
        build_config.non_determinism_reads,
    );
    let buffer = ex.buffer_non_memory.unwrap();
    let compiled_circuit: GKRCircuitArtifact<BF> =
        deserialize_json_for_test(build_config.layout_path);
    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);
    finish_proof_fixture(
        build_config.circuit_type,
        compiled_circuit,
        buffer,
        common_constants::PC_STEP as u32, // add_sub default_pc_value_in_padding
        add_sub_lui_auipc_mod::witness_eval_fn,
        &table_driver,
        &ex.decoder_table_data,
        &ex.witness_gen_data,
        build_config.compute_cpu_reference,
        build_config.device_allocator_block_log_size,
        build_config.device_allocator_arena_bytes,
        build_config.security_level,
    )
}

pub(crate) fn prepare_basic_unrolled_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: true,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
            device_allocator_arena_bytes: DEFAULT_FIXTURE_DEVICE_ARENA_BYTES,
            security_level: crate::upstream::SecurityLevel::Sec80,
        });
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected_cpu_proof
            .expect("proof fixture must include the CPU reference proof"),
    }
}

/// Sec100 variant of [`prepare_basic_unrolled_proof_fixture`]. At Sec100 the
/// per-circuit lookup-challenge and WHIR-batching PoWs are non-zero, so this
/// exercises the on-device grinding + nonce path end-to-end against the CPU
/// reference (which grinds the same PoW).
pub(crate) fn prepare_basic_unrolled_proof_fixture_sec100() -> BasicUnrolledProofFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: true,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
            device_allocator_arena_bytes: DEFAULT_FIXTURE_DEVICE_ARENA_BYTES,
            security_level: crate::upstream::SecurityLevel::Sec100,
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
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            non_determinism_reads: &[],
            compute_cpu_reference: false,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
            // NCU range replay snapshots the entire arena. The regular 64 GiB
            // fixture consumes ~143 GiB of host shared memory and is OOM-killed;
            // the measured live peak is 28.174 GiB, so 32 GiB preserves the
            // workload with enough allocator headroom for this audit fixture.
            device_allocator_arena_bytes: NCU_PROFILE_DEVICE_ARENA_BYTES,
            security_level: crate::upstream::SecurityLevel::Sec80,
        });
    assert!(
        expected_cpu_proof.is_none(),
        "profiling fixture must not compute the CPU reference proof",
    );
    fixture
}
