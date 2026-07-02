use super::*;

use super::inits_and_teardowns::{
    build_inits_and_teardowns_pages_for_test, build_inits_and_teardowns_trace_host_for_test,
};
use prover::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle;
use riscv_transpiler::witness::{BlakeGFunctionDelegationDestinationHolder, DelegationWitness};

const UNIFIED_LAYOUT_PATH: &str = "cs/compiled_circuits/unified_reduced_machine_layout_gkr.json";
const UNIFIED_NO_CACHES_LAYOUT_PATH: &str =
    "cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json";
// The default unified program: the SAME `app_blake2_g_function` the CPU unified
// test runs (its default `multi_family_smoke_blake_g_function` config), so GPU
// and CPU traces align.
const UNIFIED_BINARY_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.bin";
const UNIFIED_TEXT_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.text";

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

// Delegation cycle counts mirror the (test-gated, hence inlined here) constants
// in `prover::tests::gkr::orchestration::common`. The `prover` test module is
// not enabled by `circuit_prover`, so the values are reproduced verbatim.
const BLAKE_NUM_DELEGATION_CYCLES: usize = 1 << 20;
const BIGINT_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const KECCAK_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;

/// pr-332 removed `UnifiedRiscvCircuitOracle::new` (the oracle is now a plain
/// borrow of an externally built decoder table). Derive the unified decoder
/// table the way the production setups path does
/// (`unified_reduced_machine_circuit_setup`): `UnifiedReducedMachineDecoder`
/// over `ReducedMachineDecoderConfig` with the 5 supported CSRs. The table is
/// a function of `text_section` only.
pub(super) fn build_unified_decoder_table(
    text_section: &[u32],
) -> Vec<Option<cs::gkr_circuits::ExecutorFamilyDecoderData>> {
    use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
    use common_constants::{
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
        NON_DETERMINISM_CSR,
    };
    use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
    use cs::gkr_circuits::{process_binary_into_separate_tables_ext, OpcodeFamilyDecoder};
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;

    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[
        NON_DETERMINISM_CSR as u16,
        BLAKE2S_DELEGATION_CSR_REGISTER as u16,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
        KECCAK_SPECIAL5_CSR_REGISTER as u16,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
    ];
    let mut preprocessing_data =
        process_binary_into_separate_tables_ext::<BF, ReducedMachineDecoderConfig, true, Global>(
            text_section,
            &decoders,
            common_constants::ROM_WORD_SIZE,
            SUPPORTED_CSRS,
        );
    preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry")
}

/// Re-derives `prover::tests::gkr::orchestration::unified::build_unified_full_trace`
/// against the **non-test** prover surface (the test module is gated behind
/// `prover/test`, which circuit_prover does not enable), and also returns the
/// sparse RAM init/teardown triples the GPU page builder consumes.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_unified_full_trace_for_test(
    binary: &[u32],
    text_section: &[u32],
    unified_circuit: &GKRCircuitArtifact<BF>,
    snapshotter: &SimpleSnapshotter<DelegationsAndUnifiedCounters, { ROM_SECOND_WORD_BITS }>,
    ram: &RamWithRomRegion<{ ROM_SECOND_WORD_BITS }>,
    expected_final_state: &State<DelegationsAndUnifiedCounters>,
    tape: &SimpleTape,
    cycles_bound: usize,
    num_unified_teardown_sets: usize,
    num_calls: usize,
    run_memory_consistency_check: bool,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<BF, Global, Global>,
    TableDriver<BF>,
    Vec<UnifiedOpcodeTracingDataWithTimestamp>,
    Vec<cs::gkr_circuits::ExecutorFamilyDecoderData>,
    Vec<Vec<(u32, (common_constants::TimestampScalar, u32))>>,
) {
    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<DelegationsAndUnifiedCounters>::replay_basic_unrolled::<_, _, BF>(
        &mut state,
        &mut replay_ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);
    drop(replay_ram);

    let option_decoder_table = build_unified_decoder_table(text_section);
    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer[..],
        decoder_table: &option_decoder_table,
    };
    let unified_table_driver = build_unified_table_driver::<BF>(binary);

    // Sparse triples for the GPU page builder, AND the per-set column form for CPU witness gen.
    let sparse_inits_and_teardowns = ram.collect_inits_and_teardowns(worker, Global);
    let mut unified_inits_and_teardowns = Vec::with_capacity(num_unified_teardown_sets);
    for _ in 0..num_unified_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        unified_inits_and_teardowns.push(([a, b], [c, d]));
    }
    ram.collect_inits_and_teardowns_into_columns::<BF, _>(
        worker,
        TRACE_LEN_LOG2,
        0,
        &mut unified_inits_and_teardowns,
    );

    if run_memory_consistency_check {
        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
            unified_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            worker,
            Some(unified_inits_and_teardowns.clone()),
            Global,
            Global,
        );
        let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            unified_circuit,
            fixtures::unified_reduced_machine_mod::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &unified_table_driver,
            worker,
            Some(unified_inits_and_teardowns),
            Global,
            Global,
        );
        ensure_memory_trace_consistency(&memory_trace, &full_trace);
        let witness_gen_data = option_decoder_table
            .iter()
            .map(|entry| entry.unwrap_or_default())
            .collect_vec();
        return (
            full_trace,
            unified_table_driver,
            buffer,
            witness_gen_data,
            sparse_inits_and_teardowns,
        );
    }

    let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        unified_circuit,
        fixtures::unified_reduced_machine_mod::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &unified_table_driver,
        worker,
        Some(unified_inits_and_teardowns),
        Global,
        Global,
    );
    let witness_gen_data = option_decoder_table
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    (
        full_trace,
        unified_table_driver,
        buffer,
        witness_gen_data,
        sparse_inits_and_teardowns,
    )
}

/// Inline-prove a single (non-empty) delegation on CPU and return the FULL
/// `GKRProof`. Re-derives `prover::tests::gkr::orchestration::delegations`'
/// `prove_delegation_inner` against the non-test surface, using the same CPU
/// `example_configs` config the upstream delegation prove uses. Callers that
/// only need the grand-product factor go through `prove_delegation_factor`;
/// the proof-matrix delegation fixtures use this directly as the GPU reference.
///
/// The resulting `prover_config` (`config_for_security_level_under_pessimistic_conjecture`
/// at `num_delegation_cycles.trailing_zeros()`) is bit-identical to
/// `crate::prover::config::prover_config(CircuitType::Delegation(_), Sec80)`,
/// so the GPU `prove()` path reproduces this proof exactly.
#[allow(clippy::too_many_arguments)]
pub(super) fn prove_delegation_proof<O>(
    circuit: &GKRCircuitArtifact<BF>,
    table_driver: &TableDriver<BF>,
    oracle: &O,
    eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<'_, O, BF>,
    ),
    num_delegation_cycles: usize,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    level: SecurityLevel,
    worker: &Worker,
) -> GKRProof<BF, E4, DefaultTreeConstructor>
where
    O: cs::oracle::Oracle<BF>,
{
    let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit::<BF, _, _, _>(
        circuit,
        num_delegation_cycles,
        oracle,
        worker,
        Global,
        Global,
    );
    let full_trace = evaluate_gkr_witness_for_delegation_circuit::<BF, _, _, _>(
        circuit,
        eval_fn,
        num_delegation_cycles,
        oracle,
        table_driver,
        worker,
        Global,
        Global,
    );
    ensure_memory_trace_consistency(&memory_trace, &full_trace);
    drop(memory_trace);

    let prover_config = config_for_security_level_under_pessimistic_conjecture(
        num_delegation_cycles.trailing_zeros() as usize,
        level,
    );
    let twiddles: Twiddles<_, Global> = Twiddles::new(num_delegation_cycles, worker);
    let setup = CpuGKRSetup::construct(table_driver, &[], num_delegation_cycles, circuit);
    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        num_delegation_cycles.trailing_zeros() as usize,
        worker,
    );
    prove_configured_with_gkr::<BF, E4, DefaultTreeConstructor>(
        circuit,
        external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        Vec::new(),
        num_delegation_cycles,
        worker,
    )
}

/// Inline-prove a single delegation on CPU and return its grand-product factor
/// (`grand_product_accumulator_computed`, or `E4::ONE` when the delegation has
/// no calls). Thin wrapper over `prove_delegation_proof` that preserves the
/// empty-delegation short-circuit the unified closure path relies on.
#[allow(clippy::too_many_arguments)]
fn prove_delegation_factor<O>(
    circuit: &GKRCircuitArtifact<BF>,
    table_driver: &TableDriver<BF>,
    oracle: &O,
    eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<'_, O, BF>,
    ),
    num_delegation_cycles: usize,
    is_empty: bool,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    level: SecurityLevel,
    worker: &Worker,
) -> E4
where
    O: cs::oracle::Oracle<BF>,
{
    // Match the CPU orchestration: an empty delegation contributes ONE and is
    // not proved (the prover would assert ONE anyway). The witness-trace
    // consistency check is intentionally skipped for the empty case, exactly as
    // before (an empty delegation produces no trace to compare).
    if is_empty {
        // Still build + consistency-check the (empty) traces to preserve the
        // original behavior: `evaluate_*` over a zero-length oracle is cheap.
        let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit::<BF, _, _, _>(
            circuit,
            num_delegation_cycles,
            oracle,
            worker,
            Global,
            Global,
        );
        let full_trace = evaluate_gkr_witness_for_delegation_circuit::<BF, _, _, _>(
            circuit,
            eval_fn,
            num_delegation_cycles,
            oracle,
            table_driver,
            worker,
            Global,
            Global,
        );
        ensure_memory_trace_consistency(&memory_trace, &full_trace);
        return E4::ONE;
    }

    let proof = prove_delegation_proof(
        circuit,
        table_driver,
        oracle,
        eval_fn,
        num_delegation_cycles,
        external_challenges,
        level,
        worker,
    );
    proof.grand_product_accumulator_computed
}

/// Prove every delegation the unified program wires (the same four the CPU
/// `prove_unified` loop covers) and collect their grand-product factors so the
/// unified e2e test can close the no-filter accumulator to ONE. Delegations the
/// program never calls have a zero-length buffer -> `prove_delegation_factor`
/// short-circuits to `E4::ONE`, exactly as the CPU loop does.
fn prove_unified_delegation_factors(
    snapshotter: &SimpleSnapshotter<DelegationsAndUnifiedCounters, { ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<DelegationsAndUnifiedCounters>,
    cycles_bound: usize,
    counters: &DelegationsAndUnifiedCounters,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    worker: &Worker,
) -> Vec<E4> {
    let level = SecurityLevel::Sec80;
    let mut factors = Vec::new();

    // --- Blake2 round function (with extended control). ---
    {
        let circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(
            "cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json",
        );
        let mut table_driver = TableDriver::<BF>::new();
        cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(
            &mut table_driver,
        );

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());
        let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };
        let mut buffer = vec![DelegationWitness::empty(); counters.blake_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BlakeDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };
        ReplayerVM::<DelegationsAndUnifiedCounters>::replay_basic_unrolled::<_, _, BF>(
            &mut state,
            &mut replay_ram,
            tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );
        assert_eq!(*expected_final_state, state);
        drop(replay_ram);

        let is_empty = buffer.is_empty();
        let oracle = Blake2sDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        factors.push(prove_delegation_factor(
            &circuit,
            &table_driver,
            &oracle,
            fixtures::blake2_with_extended_control_mod::witness_eval_fn,
            BLAKE_NUM_DELEGATION_CYCLES,
            is_empty,
            external_challenges,
            level,
            worker,
        ));
    }

    // --- Bigint (with extended control). ---
    {
        let circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(
            "cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json",
        );
        let mut table_driver = TableDriver::<BF>::new();
        cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(
            &mut table_driver,
        );

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());
        let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };
        let mut buffer = vec![DelegationWitness::empty(); counters.bigint_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BigintDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };
        ReplayerVM::<DelegationsAndUnifiedCounters>::replay_basic_unrolled::<_, _, BF>(
            &mut state,
            &mut replay_ram,
            tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );
        assert_eq!(*expected_final_state, state);
        drop(replay_ram);

        let is_empty = buffer.is_empty();
        let oracle = BigintDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        factors.push(prove_delegation_factor(
            &circuit,
            &table_driver,
            &oracle,
            fixtures::bigint_with_extended_control_mod::witness_eval_fn,
            BIGINT_NUM_DELEGATION_CYCLES,
            is_empty,
            external_challenges,
            level,
            worker,
        ));
    }

    // --- Keccak special5. ---
    {
        let circuit: GKRCircuitArtifact<BF> =
            deserialize_json_for_test("cs/compiled_circuits/keccak_special5_layout_gkr.json");
        let mut table_driver = TableDriver::<BF>::new();
        cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(
            &mut table_driver,
        );

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());
        let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };
        let mut buffer = vec![DelegationWitness::empty(); counters.keccak_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = KeccakDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };
        ReplayerVM::<DelegationsAndUnifiedCounters>::replay_basic_unrolled::<_, _, BF>(
            &mut state,
            &mut replay_ram,
            tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );
        assert_eq!(*expected_final_state, state);
        drop(replay_ram);

        let is_empty = buffer.is_empty();
        let oracle = KeccakDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        factors.push(prove_delegation_factor(
            &circuit,
            &table_driver,
            &oracle,
            fixtures::keccak_special5_mod::witness_eval_fn,
            KECCAK_NUM_DELEGATION_CYCLES,
            is_empty,
            external_challenges,
            level,
            worker,
        ));
    }

    // --- Blake2 G-function (the default `app_blake2_g_function` delegation). ---
    {
        let circuit: GKRCircuitArtifact<BF> =
            deserialize_json_for_test("cs/compiled_circuits/blake2_g_function_layout_gkr.json");
        let mut table_driver = TableDriver::<BF>::new();
        cs::gkr_circuits::delegation::blake2_g_function::blake2_g_function_table_driver_fn(
            &mut table_driver,
        );

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());
        let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };
        let mut buffer = vec![DelegationWitness::empty(); counters.blake_g_function_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = BlakeGFunctionDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };
        ReplayerVM::<DelegationsAndUnifiedCounters>::replay_basic_unrolled::<_, _, BF>(
            &mut state,
            &mut replay_ram,
            tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );
        assert_eq!(*expected_final_state, state);
        drop(replay_ram);

        let is_empty = buffer.is_empty();
        let oracle = Blake2sGFunctionDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        factors.push(prove_delegation_factor(
            &circuit,
            &table_driver,
            &oracle,
            fixtures::blake2_g_function_mod::witness_eval_fn,
            BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES,
            is_empty,
            external_challenges,
            level,
            worker,
        ));
    }

    factors
}

/// Wrap a host-resident delegation witness `buffer` into the `TracingDataHost`
/// the GPU `create_transfers` consumes. Generic over the delegation witness type
/// via `DelegationTracingDataHostSource::get`, so it serves bigint / blake2 /
/// keccak alike (Task 7 generalizes the callers). The buffer rides as a single
/// chunk, mirroring the unified/per-family `*_tracing_host_for_test` helpers.
pub(super) fn make_delegation_tracing_host_for_test<W>(buffer: Vec<W>) -> TracingDataHost<Global>
where
    W: crate::prover::trace::tracing_data::DelegationTracingDataHostSource,
{
    let trace = crate::witness::trace_delegation::DelegationTraceHost::<W, Global> {
        chunks: vec![Arc::new(buffer)],
    };
    TracingDataHost::Delegation(W::get(trace))
}

/// Build a `BasicUnrolledProofFixture` that drives a single delegation circuit
/// through the GPU `prove()` path, with the CPU `prove_delegation_proof` as the
/// bit-exact reference.
///
/// A delegation fixture differs from the per-family/unified fixtures in three
/// ways, all of which `create_transfers` already tolerates:
///   * `inits_and_teardowns_host: None` — delegations prove no inits/teardowns
///     layer (the unified arm is the only producer of that bundle);
///   * the tracing host is the delegation variant (`make_delegation_tracing_host_for_test`);
///   * the decoder is gated on `compiled_circuit.has_decoder_lookup` (delegation
///     layouts have no executor-family decoder lookup, so it resolves to `None`).
///
/// The CPU reference and the GPU prove share one `ProverConfig`
/// (`prover_config(CircuitType::Delegation(_), Sec80)` ≡ the pessimistic config
/// `prove_delegation_proof` selects internally), so the proof must be field-wise
/// identical. The memory tree caps are split from the CPU proof's
/// `memory_commitment.commitment.cap`, the same idiom the other fixtures use.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_delegation_proof_fixture<O, W>(
    circuit_type: DelegationCircuitType,
    layout_path: &str,
    table_driver: TableDriver<BF>,
    buffer: Vec<W>,
    oracle: O,
    witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<'_, O, BF>,
    ),
    num_delegation_cycles: usize,
) -> BasicUnrolledProofFixture
where
    O: cs::oracle::Oracle<BF>,
    W: crate::prover::trace::tracing_data::DelegationTracingDataHostSource,
{
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;
    const HOST_POOL_SIZE_MB: usize = 1024;
    let device_allocator_arena_bytes: usize = 64usize << 30;
    let device_allocator_block_log_size = default_fixture_device_allocator_block_log_size();

    assert!(
        !buffer.is_empty(),
        "delegation proof fixture requires a non-empty delegation buffer \
         (an empty delegation produces no proof to compare); \
         the selected workload must exercise the {circuit_type:?} delegation",
    );

    let worker = Worker::new_with_num_threads(8);
    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(layout_path);
    assert_eq!(
        compiled_circuit.trace_len, num_delegation_cycles,
        "delegation circuit trace_len must equal num_delegation_cycles",
    );

    let external_challenges = test_external_challenges();
    let fixture_circuit_type = CircuitType::Delegation(circuit_type);
    let prover_config = delegation_prover_config(circuit_type);
    let whir_schedule = prover_config.whir_schedule.clone();

    // CPU reference proof (the full `GKRProof`, not just the grand-product
    // factor): the GPU `prove()` below must reproduce it bit-for-bit.
    let expected_cpu_proof = prove_delegation_proof(
        &compiled_circuit,
        &table_driver,
        &oracle,
        witness_eval_fn,
        num_delegation_cycles,
        &external_challenges,
        SecurityLevel::Sec80,
        &worker,
    );
    eprintln!("delegation fixture ({circuit_type:?}): cpu proof ready");

    // GPU setup host — delegations commit with no decoder table (`&[]`) and use
    // `whir_steps_schedule[0]` rows-per-leaf, matching `delegation_asserts.rs`'s
    // validated delegation setup. (`prove()` asserts this equals
    // `base_oracles_values_per_leaf.trailing_zeros()`.)
    let setup =
        CpuGKRSetup::construct(&table_driver, &[], num_delegation_cycles, &compiled_circuit);
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
            whir_schedule.whir_steps_schedule[0] as u32,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );

    // Delegation layouts carry no executor-family decoder lookup, so this host
    // is unused (create_transfers gates on `has_decoder_lookup`); build a benign
    // empty one to satisfy the `BasicUnrolledFixture` field.
    let decoder_table_host = make_decoder_table_host_for_test(&[]);

    // Per-coset memory tree caps from the CPU proof.
    let combined_cap = &expected_cpu_proof
        .whir_proof
        .memory_commitment
        .commitment
        .cap;
    let lde_factor = whir_schedule.base_lde_factor;
    let subcap_size = combined_cap.cap.len() / lde_factor;
    let memory_tree_caps = combined_cap
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec();

    let tracing_data_host = make_delegation_tracing_host_for_test(buffer);
    eprintln!("delegation fixture ({circuit_type:?}): tracing host ready");

    let base = BasicUnrolledFixture {
        context,
        circuit_type: fixture_circuit_type,
        compiled_circuit,
        external_challenges,
        prover_config,
        final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
        gpu_setup_host: Some(gpu_setup_host),
        decoder_table_host,
        tracing_data_host,
        memory_tree_caps,
        // Delegations prove no inits-and-teardowns layer and carry no
        // unified-closure metadata.
        inits_and_teardowns_host: None,
        unified_register_final_state: [(0u32, (0u32, 0u32)); 32],
        unified_final_pc: 0,
        unified_final_timestamp: 0,
        delegation_grand_product_factors: Vec::new(),
    };
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof,
    }
}

/// Profiling variant: same delegation fixture, no CPU reference proof. Returns
/// just the `BasicUnrolledFixture` for `run_profile`.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_delegation_profiling_fixture<O, W>(
    circuit_type: DelegationCircuitType,
    layout_path: &str,
    table_driver: TableDriver<BF>,
    buffer: Vec<W>,
    _oracle: O,
    _witness_eval_fn: fn(
        &mut prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<'_, O, BF>,
    ),
    num_delegation_cycles: usize,
) -> BasicUnrolledFixture
where
    O: cs::oracle::Oracle<BF>,
    W: crate::prover::trace::tracing_data::DelegationTracingDataHostSource,
{
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;
    const HOST_POOL_SIZE_MB: usize = 1024;
    let device_allocator_arena_bytes: usize = 64usize << 30;
    let device_allocator_block_log_size = default_fixture_device_allocator_block_log_size();

    assert!(
        !buffer.is_empty(),
        "delegation profiling fixture requires a non-empty delegation buffer",
    );

    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(layout_path);
    assert_eq!(compiled_circuit.trace_len, num_delegation_cycles);

    let external_challenges = test_external_challenges();
    let fixture_circuit_type = CircuitType::Delegation(circuit_type);
    let prover_config = delegation_prover_config(circuit_type);
    let whir_schedule = prover_config.whir_schedule.clone();

    let setup =
        CpuGKRSetup::construct(&table_driver, &[], num_delegation_cycles, &compiled_circuit);
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
            whir_schedule.whir_steps_schedule[0] as u32,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );
    let decoder_table_host = make_decoder_table_host_for_test(&[]);
    let tracing_data_host = make_delegation_tracing_host_for_test(buffer);

    // No CPU reference -> derive memory tree caps from a one-shot GPU
    // commit_memory (delegations need no decoder / inits-and-teardowns bundle).
    let memory_tree_caps = {
        let mut tracing_data_transfer =
            TracingDataTransfer::new(tracing_data_host.clone(), &context).unwrap();
        let transfer = crate::prover::transfer::single_shot_h2d(
            |t| tracing_data_transfer.schedule_transfer(t, &context),
            &context,
        )
        .unwrap();
        transfer.ensure_transferred(&context).unwrap();
        let job = commit_memory(
            fixture_circuit_type,
            &compiled_circuit,
            None,
            &tracing_data_transfer.data_device,
            &prover_config,
            &context,
        )
        .unwrap();
        let (tree_caps, _) = job.finish().unwrap();
        drop(transfer);
        drop(tracing_data_transfer);
        tree_caps
    };

    BasicUnrolledFixture {
        context,
        circuit_type: fixture_circuit_type,
        compiled_circuit,
        external_challenges,
        prover_config,
        final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
        gpu_setup_host: Some(gpu_setup_host),
        decoder_table_host,
        tracing_data_host,
        memory_tree_caps,
        inits_and_teardowns_host: None,
        unified_register_final_state: [(0u32, (0u32, 0u32)); 32],
        unified_final_pc: 0,
        unified_final_timestamp: 0,
        delegation_grand_product_factors: Vec::new(),
    }
}

pub(crate) fn prepare_unified_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_unified_proof_fixture_with_layout(UNIFIED_LAYOUT_PATH)
}

pub(crate) fn prepare_unified_no_caches_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_unified_proof_fixture_with_layout(UNIFIED_NO_CACHES_LAYOUT_PATH)
}

/// Unified fixture WITHOUT a CPU reference proof, for the profile test (which only
/// checks proof structure + device-memory behavior, so it skips the expensive CPU
/// unified prove).
pub(crate) fn prepare_unified_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unified_fixture(UNIFIED_LAYOUT_PATH, false).0
}

pub(crate) fn prepare_unified_proof_fixture_with_layout(
    layout_path: &str,
) -> BasicUnrolledProofFixture {
    let (base, expected_cpu_proof) = prepare_unified_fixture(layout_path, true);
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected_cpu_proof
            .expect("unified proof fixture must include the CPU reference proof"),
    }
}

fn prepare_unified_fixture(
    layout_path: &str,
    compute_cpu_reference: bool,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    type CountersT = DelegationsAndUnifiedCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;
    const HOST_POOL_SIZE_MB: usize = 1024;
    let device_allocator_arena_bytes: usize = 64usize << 30;
    let device_allocator_block_log_size = default_fixture_device_allocator_block_log_size();

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let binary = read_test_words(UNIFIED_BINARY_PATH);
    let text_section = read_test_words(UNIFIED_TEXT_PATH);

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

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    // Closure-assembly metadata, captured from the final VM state (counters
    // zeroed for the boundary state the replayer must reproduce).
    let counters = state.counters;
    let unified_register_final_state: [(u32, (u32, u32)); 32] = state
        .registers
        .map(|el| (el.value, split_timestamp(el.timestamp)));
    let unified_final_pc = state.pc;
    let unified_final_timestamp = state.timestamp;
    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let compiled_circuit: GKRCircuitArtifact<BF> = deserialize_json_for_test(layout_path);
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
            compute_cpu_reference,
            &worker,
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

    let fixture_circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    let prover_config =
        crate::prover::config::prover_config(fixture_circuit_type, SecurityLevel::Sec80).unwrap();
    let whir_schedule = prover_config.whir_schedule.clone();

    // The CPU setup needs the genuine `Option<..>` decoder table (the `None`
    // rows encode the `MINUS_ONE` fill, which differs from `Some(default)`);
    // the GPU host below uses the unwrapped form + its own fill value.
    let option_decoder_table = build_unified_decoder_table(&text_section);
    let setup = CpuGKRSetup::construct(
        &unified_table_driver,
        &option_decoder_table,
        trace_len,
        &compiled_circuit,
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
    let decoder_table_host = make_decoder_table_host_for_test(&witness_gen_data);

    // Sparse i/t triples -> page-based GPU wire format -> transfer host.
    let (page_indices, values_packed, timestamps_packed) = build_inits_and_teardowns_pages_for_test(
        &sparse_inits_and_teardowns,
        TRACE_LEN_LOG2 as u32,
        num_unified_teardown_sets as u32,
    );
    let inits_and_teardowns_host = build_inits_and_teardowns_trace_host_for_test(
        &page_indices,
        &values_packed,
        &timestamps_packed,
    );

    let (expected_cpu_proof, delegation_grand_product_factors) = if compute_cpu_reference {
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
            (0..num_unified_teardown_sets as u32).collect::<Vec<u32>>(),
            trace_len,
            &worker,
        );

        // Prove the active delegations so Task 22 can close the no-filter
        // grand-product accumulator to ONE.
        let factors = prove_unified_delegation_factors(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            &counters,
            &external_challenges,
            &worker,
        );
        (Some(expected_cpu_proof), factors)
    } else {
        (None, Vec::new())
    };

    let tracing_data_host = make_unified_tracing_host_for_test(buffer);

    // Per-coset memory tree caps from the CPU proof (needed for the prove signature).
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
        // No CPU reference -> derive caps from a one-shot GPU commit_memory.
        // The unified arm requires the inits/teardowns bundle, so use
        // `commit_memory_from_transfers` (the 6-arg `commit_memory` hard-codes
        // `None` for i/t and panics on a unified circuit with "requires
        // init/teardown data"). No setup transfer is needed — the commit-memory
        // bundle only carries decoder/i-t/tracing. Validated bit-exact vs CPU by
        // `run_unified_commit_memory_matches_cpu_test`.
        let decoder = if compiled_circuit.has_decoder_lookup {
            Some(DecoderTableTransfer::new(Arc::clone(&decoder_table_host), &context).unwrap())
        } else {
            None
        };
        let inits_and_teardowns = Some(
            InitsAndTeardownsTransfer::new(inits_and_teardowns_host.clone(), &context).unwrap(),
        );
        let tracing_data =
            Some(TracingDataTransfer::new(tracing_data_host.clone(), &context).unwrap());

        let mut bundle = crate::prover::trace::memory_transfer::GpuGKRCommitMemoryTransfer::new(
            decoder,
            inits_and_teardowns,
            tracing_data,
            &context,
        )
        .unwrap();
        bundle.schedule(&context).unwrap();

        let job = crate::prover::trace::memory::commit_memory_from_transfers(
            fixture_circuit_type,
            &compiled_circuit,
            bundle,
            &prover_config,
            &context,
        )
        .unwrap();
        let (tree_caps, _) = job.finish().unwrap();
        tree_caps
    };

    (
        BasicUnrolledFixture {
            context,
            circuit_type: fixture_circuit_type,
            compiled_circuit,
            external_challenges,
            prover_config,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host: Some(gpu_setup_host),
            decoder_table_host,
            tracing_data_host,
            memory_tree_caps,
            inits_and_teardowns_host: Some(inits_and_teardowns_host),
            unified_register_final_state,
            unified_final_pc,
            unified_final_timestamp,
            delegation_grand_product_factors,
        },
        expected_cpu_proof,
    )
}
