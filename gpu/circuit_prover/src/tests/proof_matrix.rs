use super::*;

// ---------------------------------------------------------------------------
// Generic test bodies
// ---------------------------------------------------------------------------

/// The windowed-arm options every both-arm wrapper requests.
fn windowed_options() -> GkrBackwardOptions {
    GkrBackwardOptions {
        windowed_r0: true,
        ..GkrBackwardOptions::default()
    }
}

/// The per-round arm, pinned so a both-arm wrapper keeps comparing two arms
/// regardless of which one the defaults select.
fn per_round_options() -> GkrBackwardOptions {
    GkrBackwardOptions {
        windowed_r0: false,
        ..GkrBackwardOptions::default()
    }
}

/// Full GPU proof == CPU reference, on BOTH backward arms in the same binary.
///
/// The per-round arm always runs. The windowed arm runs whenever this family's
/// validated schedule class selects it, and is then compared against the CPU
/// fixture AND, serialized, against the per-round arm's own bytes — the
/// arm-vs-arm equality the windowed R0 integration is contracted on. A family
/// whose config does not select the windowed arm must say so through
/// `resolve_backward_execution_strategy`, so a schedule-class change cannot
/// silently turn a both-arm row into a second per-round run.
pub(super) fn run_proof_parity(fixture: &BasicUnrolledProofFixture) {
    let (per_round, _ms) = fixture
        .schedule_prove_with(per_round_options())
        .unwrap()
        .finish()
        .unwrap();
    assert_gkr_proof_eq_for_test(&per_round, &fixture.expected_cpu_proof);

    let strategy = crate::proof::resolve_backward_execution_strategy(
        &fixture.base.gkr_programs,
        &fixture.base.prover_config,
        windowed_options(),
    );
    eprintln!("proof_parity backward arms: per-round + {strategy:?}");
    if strategy != gpu_gkr::BackwardExecutionStrategy::WindowedR0 {
        assert_eq!(
            strategy,
            gpu_gkr::BackwardExecutionStrategy::PerRound,
            "an arm this wrapper does not know how to gate",
        );
        return;
    }
    let (windowed, _ms) = fixture
        .schedule_prove_with(windowed_options())
        .unwrap()
        .finish()
        .unwrap();
    assert_gkr_proof_eq_for_test(&windowed, &fixture.expected_cpu_proof);
    assert_serialized_proof_bytes_eq(&per_round, &windowed);
}

/// Two concurrently-scheduled proofs on a recycled-block arena (the
/// uninitialized-witness regression guard). schedule -> schedule -> finish -> finish.
///
/// The second job takes the windowed arm wherever the family selects it, so the
/// arena-recycling guard covers both arms without a third proof: both are
/// compared against the CPU fixture, and their serialized bytes against each
/// other.
pub(super) fn run_multi_schedule(fixture: &BasicUnrolledProofFixture) {
    let baseline = fixture.base.context.get_used_mem_current();
    let strategy = crate::proof::resolve_backward_execution_strategy(
        &fixture.base.gkr_programs,
        &fixture.base.prover_config,
        windowed_options(),
    );
    eprintln!("multi_schedule backward arms: per-round + {strategy:?}");
    let job0 = fixture.schedule_prove_with(per_round_options()).unwrap();
    let job1 = fixture.schedule_prove_with(windowed_options()).unwrap();
    let (p0, ms0) = job0.finish().unwrap();
    eprintln!("proof_job_0 proof time: {ms0} ms");
    assert_gkr_proof_eq_for_test(&p0, &fixture.expected_cpu_proof);
    let (p1, ms1) = job1.finish().unwrap();
    eprintln!("proof_job_1 proof time: {ms1} ms");
    assert_gkr_proof_eq_for_test(&p1, &fixture.expected_cpu_proof);
    assert_serialized_proof_bytes_eq(&p0, &p1);
    drop(p0);
    drop(p1);
    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline,
        "device memory must return to baseline after both proofs complete"
    );
}

/// Warmup + profiled prove; structure check only (no CPU reference needed).
pub(super) fn run_profile(fixture: &BasicUnrolledFixture) {
    let baseline = fixture.context.get_used_mem_current();
    let warm = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let warm_job = fixture.prove(warm).unwrap();
    let (warm_proof, warm_ms) = warm_job.finish().unwrap();
    eprintln!("warmup proof time: {warm_ms} ms");
    assert_gkr_proof_structure_for_test(&warm_proof, &fixture.prover_config.whir_schedule);
    drop(warm_proof);
    let prof = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    fixture.context.reset_used_mem_peak();
    let (prof_proof, prof_ms) = {
        let _range = scoped_range(
            Some("gpu_circuit_prover.tests"),
            "test.gpu.prove.profiled_call",
        );
        fixture.prove(prof).unwrap().finish().unwrap()
    };
    eprintln!("profiled proof time: {prof_ms} ms");
    assert_gkr_proof_structure_for_test(&prof_proof, &fixture.prover_config.whir_schedule);
    drop(prof_proof);
    let peak = fixture.context.get_used_mem_peak();
    eprintln!(
        "peak device memory: {:.3} GiB",
        peak as f64 / (1u64 << 30) as f64
    );
    assert!(peak > baseline);
    assert_eq!(fixture.context.get_used_mem_current(), baseline);
}

#[cfg(feature = "task8_continuation_differential_test")]
fn task8_blake2s_digest(bytes: &[u8]) -> String {
    use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS};

    // The byte length is part of the message and the tail is zero padded, so
    // distinct JSON byte strings cannot alias merely because the u32 API has a
    // word-granular final length.
    let mut framed = Vec::with_capacity(8 + bytes.len() + 3);
    framed.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    framed.extend_from_slice(bytes);
    framed.resize(framed.len().next_multiple_of(4), 0);
    let words: Vec<u32> = framed
        .as_chunks::<4>()
        .0
        .iter()
        .map(|chunk| u32::from_le_bytes(*chunk))
        .collect();
    let mut state = Blake2sState::new();
    let mut chunks = words.chunks(BLAKE2S_BLOCK_SIZE_U32_WORDS).peekable();
    let mut digest = [0u32; blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS];
    while let Some(chunk) = chunks.next() {
        let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        block[..chunk.len()].copy_from_slice(chunk);
        if chunks.peek().is_some() {
            state.absorb::<false>(&block);
        } else {
            state.absorb_final_block::<false>(&block, chunk.len(), &mut digest);
        }
    }
    digest
        .iter()
        .flat_map(|word| word.to_le_bytes())
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[cfg(feature = "task8_continuation_differential_test")]
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
struct Task8AllocatorConfiguration {
    powers_of_w_coarse_log_count: u32,
    allocator_block_log_size: u32,
    device_slack_static_bytes: usize,
    device_slack_per_thread_bytes: usize,
    max_device_allocation_blocks_count: Option<usize>,
    host_allocator_block_log_size: u32,
    host_allocator_blocks_count: usize,
    actual_device_allocation_blocks_count: usize,
    actual_device_arena_bytes: usize,
    small_allocator_enabled: bool,
    small_allocator_log_chunk_size: Option<u32>,
    small_allocator_pool_blocks: usize,
}

#[cfg(feature = "task8_continuation_differential_test")]
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
struct Task8MemoryIntervalRecord {
    start_physical_backing_bytes: usize,
    start_logical_live_bytes: usize,
    peak_physical_backing_bytes: usize,
    peak_logical_live_bytes: usize,
    summed_requested_bytes: usize,
    peak_window_end_physical_backing_bytes: usize,
    peak_window_end_logical_live_bytes: usize,
    return_physical_backing_bytes: usize,
    return_logical_live_bytes: usize,
}

#[cfg(feature = "task8_continuation_differential_test")]
impl From<gpu_prover_context::PoolMemoryHighWaterReport> for Task8MemoryIntervalRecord {
    fn from(report: gpu_prover_context::PoolMemoryHighWaterReport) -> Self {
        Self {
            start_physical_backing_bytes: report.start.physical_backing_bytes,
            start_logical_live_bytes: report.start.logical_live_bytes,
            peak_physical_backing_bytes: report.physical_backing_peak_bytes,
            peak_logical_live_bytes: report.logical_live_peak_bytes,
            summed_requested_bytes: report.summed_requested_bytes,
            peak_window_end_physical_backing_bytes: report.peak_window_end.physical_backing_bytes,
            peak_window_end_logical_live_bytes: report.peak_window_end.logical_live_bytes,
            return_physical_backing_bytes: report.return_to_entry.physical_backing_bytes,
            return_logical_live_bytes: report.return_to_entry.logical_live_bytes,
        }
    }
}

#[cfg(feature = "task8_continuation_differential_test")]
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
struct Task8RuntimeOperationCensus {
    initial_input_h2d: usize,
    final_slab_d2h: usize,
    proof_assembly_after_final_d2h: usize,
    candidate_added_h2d: usize,
    candidate_added_d2h: usize,
    candidate_added_host_callbacks: usize,
    candidate_added_host_staging: usize,
    candidate_added_host_computation: usize,
}

#[cfg(feature = "task8_continuation_differential_test")]
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
struct Task8ExactMemoryRecord {
    schema_version: u32,
    harness_contract: String,
    artifact_head: String,
    artifact_tree: String,
    release_executable: String,
    workload_id: String,
    sample_index: usize,
    pair_index: usize,
    order_in_pair: usize,
    arm: String,
    backward_options: String,
    final_trace_size_log_2: u32,
    configuration: Task8AllocatorConfiguration,
    backward: Task8MemoryIntervalRecord,
    whole: Task8MemoryIntervalRecord,
    proof_blake2s: String,
    proof_serialized_bytes: usize,
    proof_time_ms_bits: u32,
    selected_strategy: String,
    main_folding_steps: usize,
    main_layer_count: usize,
    main_r0_launch_count: usize,
    main_continuation_planned_window_count: usize,
    main_tail_launch_count: usize,
    legacy_layer_count: usize,
    legacy_round_count: usize,
    operation_trace: Vec<crate::proof::MainAcceptanceOperation>,
    runtime_operation_census: Task8RuntimeOperationCensus,
}

#[cfg(feature = "task8_continuation_differential_test")]
fn validate_exact_memory_return_chain(
    arm: &str,
    backward: Task8MemoryIntervalRecord,
    whole: Task8MemoryIntervalRecord,
) -> Result<(), String> {
    if whole.return_physical_backing_bytes != whole.start_physical_backing_bytes {
        return Err(format!(
            "{arm} whole physical return-to-entry mismatch: start={} return={}",
            whole.start_physical_backing_bytes, whole.return_physical_backing_bytes
        ));
    }
    if whole.return_logical_live_bytes != whole.start_logical_live_bytes {
        return Err(format!(
            "{arm} whole logical return-to-entry mismatch: start={} return={}",
            whole.start_logical_live_bytes, whole.return_logical_live_bytes
        ));
    }
    if backward.return_physical_backing_bytes != whole.return_physical_backing_bytes {
        return Err(format!(
            "{arm} backward physical return-to-entry mismatch against whole return: backward_return={} whole_return={}",
            backward.return_physical_backing_bytes, whole.return_physical_backing_bytes
        ));
    }
    if backward.return_logical_live_bytes != whole.return_logical_live_bytes {
        return Err(format!(
            "{arm} backward logical return-to-entry mismatch against whole return: backward_return={} whole_return={}",
            backward.return_logical_live_bytes, whole.return_logical_live_bytes
        ));
    }
    Ok(())
}

#[cfg(feature = "task8_continuation_differential_test")]
fn compare_task8_exact_memory(
    baseline: &Task8ExactMemoryRecord,
    new: &Task8ExactMemoryRecord,
) -> Result<(), String> {
    if baseline.schema_version != 2 || new.schema_version != 2 {
        return Err("Task 8 row has an unsupported schema version".to_owned());
    }
    if baseline.harness_contract != "main-integrated-production-vs-whole-legacy-v1"
        || new.harness_contract != baseline.harness_contract
    {
        return Err("Task 8 integrated harness contract differs".to_owned());
    }
    if baseline.arm != "legacy"
        || new.arm != "production"
        || !baseline.backward_options.contains("windowed_r0: false")
        || !baseline
            .backward_options
            .contains("windowed_main_continuations: false")
        || !new.backward_options.contains("windowed_r0: true")
        || !new
            .backward_options
            .contains("windowed_main_continuations: true")
    {
        return Err("Task 8 paired rows have invalid arm/options labels".to_owned());
    }
    if baseline.selected_strategy != "PerRound" || new.selected_strategy != "WindowedR0" {
        return Err(
            "Task 8 paired rows did not select whole-layer legacy and production MAIN".to_owned(),
        );
    }
    if baseline.configuration != new.configuration {
        return Err("Task 8 allocator configuration differs between arms".to_owned());
    }
    if baseline.main_continuation_planned_window_count != 0
        || baseline.main_r0_launch_count != 0
        || baseline.main_tail_launch_count != 0
        || baseline.legacy_layer_count == 0
        || baseline.legacy_round_count == 0
    {
        return Err("Task 8 legacy/off row has invalid planned work counts".to_owned());
    }
    if new.main_continuation_planned_window_count == 0
        || new.main_r0_launch_count == 0
        || new.main_tail_launch_count == 0
        || new.legacy_layer_count != 0
        || new.legacy_round_count != 0
    {
        return Err("Task 8 new/on row has invalid planned work counts".to_owned());
    }
    if baseline.main_layer_count == 0
        || baseline.main_layer_count != new.main_layer_count
        || baseline.main_folding_steps != new.main_folding_steps
        || new.main_r0_launch_count != new.main_layer_count
        || new.main_tail_launch_count != new.main_layer_count
        || baseline.legacy_layer_count != baseline.main_layer_count
    {
        return Err("Task 8 paired rows have invalid MAIN layer coverage".to_owned());
    }
    if baseline.artifact_head != new.artifact_head
        || baseline.artifact_tree != new.artifact_tree
        || baseline.release_executable != new.release_executable
        || baseline.workload_id != new.workload_id
        || baseline.pair_index != new.pair_index
        || baseline.final_trace_size_log_2 != new.final_trace_size_log_2
    {
        return Err("Task 8 paired-arm provenance differs".to_owned());
    }
    let expected_order = if baseline.pair_index % 2 == 0 {
        baseline.order_in_pair == 0
            && new.order_in_pair == 1
            && baseline.sample_index.checked_add(1) == Some(new.sample_index)
    } else {
        baseline.order_in_pair == 1
            && new.order_in_pair == 0
            && new.sample_index.checked_add(1) == Some(baseline.sample_index)
    };
    if !expected_order
        || baseline.sample_index / 2 != baseline.pair_index
        || new.sample_index / 2 != new.pair_index
    {
        return Err("Task 8 paired rows have invalid A,B/B,A sample orientation".to_owned());
    }
    if baseline.proof_blake2s != new.proof_blake2s
        || baseline.proof_serialized_bytes != new.proof_serialized_bytes
    {
        return Err("Task 8 paired-arm proof bytes differ".to_owned());
    }
    let expected_trace = expected_task8_operation_trace();
    for (arm, record) in [("legacy", baseline), ("production", new)] {
        if record.operation_trace != expected_trace {
            return Err(format!(
                "Task 8 {arm} runtime operation trace is incomplete or reordered"
            ));
        }
        let census = &record.runtime_operation_census;
        if census.initial_input_h2d != 1
            || census.final_slab_d2h != 1
            || census.proof_assembly_after_final_d2h != 1
            || census.candidate_added_h2d != 0
            || census.candidate_added_d2h != 0
            || census.candidate_added_host_callbacks != 0
            || census.candidate_added_host_staging != 0
            || census.candidate_added_host_computation != 0
        {
            return Err(format!("Task 8 {arm} runtime operation census is invalid"));
        }
    }
    for (name, left, right) in [
        ("backward", baseline.backward, new.backward),
        ("whole", baseline.whole, new.whole),
    ] {
        if left.start_physical_backing_bytes != right.start_physical_backing_bytes {
            return Err(format!(
                "{name} physical entry current differs between arms"
            ));
        }
        if left.start_logical_live_bytes != right.start_logical_live_bytes {
            return Err(format!("{name} logical entry current differs between arms"));
        }
    }
    validate_exact_memory_return_chain("baseline", baseline.backward, baseline.whole)?;
    validate_exact_memory_return_chain("new", new.backward, new.whole)?;
    for (interval, metric, baseline_bytes, new_bytes) in [
        (
            "backward",
            "physical_backing",
            baseline.backward.peak_physical_backing_bytes,
            new.backward.peak_physical_backing_bytes,
        ),
        (
            "backward",
            "logical_live",
            baseline.backward.peak_logical_live_bytes,
            new.backward.peak_logical_live_bytes,
        ),
        (
            "whole",
            "physical_backing",
            baseline.whole.peak_physical_backing_bytes,
            new.whole.peak_physical_backing_bytes,
        ),
        (
            "whole",
            "logical_live",
            baseline.whole.peak_logical_live_bytes,
            new.whole.peak_logical_live_bytes,
        ),
    ] {
        if new_bytes > baseline_bytes {
            return Err(format!(
                "Task 8 {interval} {metric} peak increased: baseline={baseline_bytes} new={new_bytes} delta=+{}",
                new_bytes - baseline_bytes
            ));
        }
    }
    for (interval, baseline_bytes, new_bytes) in [
        (
            "backward",
            baseline.backward.summed_requested_bytes,
            new.backward.summed_requested_bytes,
        ),
        (
            "whole",
            baseline.whole.summed_requested_bytes,
            new.whole.summed_requested_bytes,
        ),
    ] {
        if new_bytes > baseline_bytes {
            return Err(format!(
                "Task 8 {interval} requested bytes increased: baseline={baseline_bytes} new={new_bytes} delta=+{}",
                new_bytes - baseline_bytes
            ));
        }
    }
    Ok(())
}

#[cfg(feature = "task8_continuation_differential_test")]
fn expected_task8_operation_trace() -> Vec<crate::proof::MainAcceptanceOperation> {
    vec![
        crate::proof::MainAcceptanceOperation::InitialInputsTransferEnsured,
        crate::proof::MainAcceptanceOperation::Stage1AndForwardPrepared,
        crate::proof::MainAcceptanceOperation::ForwardScheduled,
        crate::proof::MainAcceptanceOperation::BackwardHandoffPrepared,
        crate::proof::MainAcceptanceOperation::BackwardObserverStarted,
        crate::proof::MainAcceptanceOperation::BackwardScheduled,
        crate::proof::MainAcceptanceOperation::BackwardObserverSealed,
        crate::proof::MainAcceptanceOperation::WhirScheduled,
        crate::proof::MainAcceptanceOperation::FinalSlabD2hAndProofAssemblyScheduled,
        crate::proof::MainAcceptanceOperation::ProofOwnedDeviceBuffersReleased,
        crate::proof::MainAcceptanceOperation::ProofJobReturned,
        crate::proof::MainAcceptanceOperation::ProofJobFinished,
        crate::proof::MainAcceptanceOperation::BackwardObserverFinished,
        crate::proof::MainAcceptanceOperation::WholeObserverFinished,
    ]
}

#[cfg(feature = "task8_continuation_differential_test")]
fn equal_task8_memory_record() -> Task8ExactMemoryRecord {
    let whole = Task8MemoryIntervalRecord {
        start_physical_backing_bytes: 100,
        start_logical_live_bytes: 90,
        peak_physical_backing_bytes: 120,
        peak_logical_live_bytes: 110,
        summed_requested_bytes: 25,
        peak_window_end_physical_backing_bytes: 115,
        peak_window_end_logical_live_bytes: 105,
        return_physical_backing_bytes: 100,
        return_logical_live_bytes: 90,
    };
    let backward = Task8MemoryIntervalRecord {
        start_physical_backing_bytes: 110,
        start_logical_live_bytes: 100,
        peak_physical_backing_bytes: 130,
        peak_logical_live_bytes: 120,
        summed_requested_bytes: 25,
        peak_window_end_physical_backing_bytes: 115,
        peak_window_end_logical_live_bytes: 105,
        return_physical_backing_bytes: 100,
        return_logical_live_bytes: 90,
    };
    Task8ExactMemoryRecord {
        schema_version: 2,
        harness_contract: "main-integrated-production-vs-whole-legacy-v1".to_owned(),
        artifact_head: "head".to_owned(),
        artifact_tree: "tree".to_owned(),
        release_executable: "/durable/test-binary".to_owned(),
        workload_id: "mutation".to_owned(),
        sample_index: 0,
        pair_index: 0,
        order_in_pair: 0,
        arm: "legacy".to_owned(),
        backward_options:
            "GkrBackwardOptions { windowed_r0: false, windowed_main_continuations: false }"
                .to_owned(),
        final_trace_size_log_2: 24,
        configuration: Task8AllocatorConfiguration {
            powers_of_w_coarse_log_count: 13,
            allocator_block_log_size: 20,
            device_slack_static_bytes: 1 << 27,
            device_slack_per_thread_bytes: 1 << 11,
            max_device_allocation_blocks_count: Some(64 << 10),
            host_allocator_block_log_size: 13,
            host_allocator_blocks_count: 163_840,
            actual_device_allocation_blocks_count: 64 << 10,
            actual_device_arena_bytes: 64usize << 30,
            small_allocator_enabled: true,
            small_allocator_log_chunk_size: Some(8),
            small_allocator_pool_blocks: 16,
        },
        backward,
        whole,
        proof_blake2s: "00".repeat(32),
        proof_serialized_bytes: 4096,
        proof_time_ms_bits: 0,
        selected_strategy: "PerRound".to_owned(),
        main_folding_steps: 23,
        main_layer_count: 1,
        main_r0_launch_count: 0,
        main_continuation_planned_window_count: 0,
        main_tail_launch_count: 0,
        legacy_layer_count: 1,
        legacy_round_count: 23,
        operation_trace: expected_task8_operation_trace(),
        runtime_operation_census: Task8RuntimeOperationCensus {
            initial_input_h2d: 1,
            final_slab_d2h: 1,
            proof_assembly_after_final_d2h: 1,
            candidate_added_h2d: 0,
            candidate_added_d2h: 0,
            candidate_added_host_callbacks: 0,
            candidate_added_host_staging: 0,
            candidate_added_host_computation: 0,
        },
    }
}

#[cfg(feature = "task8_continuation_differential_test")]
fn paired_new_task8_memory_record() -> Task8ExactMemoryRecord {
    let mut record = equal_task8_memory_record();
    record.arm = "production".to_owned();
    record.sample_index = 1;
    record.order_in_pair = 1;
    record.backward_options =
        "GkrBackwardOptions { windowed_r0: true, windowed_main_continuations: true }".to_owned();
    record.selected_strategy = "WindowedR0".to_owned();
    record.main_r0_launch_count = 1;
    record.main_continuation_planned_window_count = 1;
    record.main_tail_launch_count = 1;
    record.legacy_layer_count = 0;
    record.legacy_round_count = 0;
    record
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_comparator_rejects_each_positive_byte_delta() {
    let baseline = equal_task8_memory_record();
    for (case, label) in [
        (0, "backward physical_backing"),
        (1, "backward logical_live"),
        (2, "whole physical_backing"),
        (3, "whole logical_live"),
    ] {
        let mut new = paired_new_task8_memory_record();
        match case {
            0 => new.backward.peak_physical_backing_bytes += 1,
            1 => new.backward.peak_logical_live_bytes += 1,
            2 => new.whole.peak_physical_backing_bytes += 1,
            3 => new.whole.peak_logical_live_bytes += 1,
            _ => unreachable!(),
        }
        let error = compare_task8_exact_memory(&baseline, &new).unwrap_err();
        assert!(error.contains(label), "{error}");
    }
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_integrated_comparator_rejects_requested_byte_growth() {
    let baseline = equal_task8_memory_record();
    for interval in ["backward", "whole"] {
        let mut production = paired_new_task8_memory_record();
        if interval == "backward" {
            production.backward.summed_requested_bytes += 1;
        } else {
            production.whole.summed_requested_bytes += 1;
        }
        let error = compare_task8_exact_memory(&baseline, &production).unwrap_err();
        assert!(
            error.contains(&format!("{interval} requested bytes")),
            "{error}"
        );
    }
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_integrated_comparator_rejects_trace_and_coverage_mutations() {
    let baseline = equal_task8_memory_record();
    let production = paired_new_task8_memory_record();

    let mut mutated = production.clone();
    mutated.operation_trace.remove(5);
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("operation trace"));

    let mut mutated = production.clone();
    mutated.main_continuation_planned_window_count = 0;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("planned work counts"));

    let mut mutated = production;
    mutated.main_tail_launch_count = 0;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("planned work counts"));
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_integrated_proof_digest_is_mutation_sensitive() {
    let bytes = br#"{"proof":"stable"}"#;
    let digest = task8_blake2s_digest(bytes);
    let mut mutated = bytes.to_vec();
    *mutated.last_mut().unwrap() ^= 1;
    assert_ne!(digest, task8_blake2s_digest(&mutated));
    assert_eq!(digest.len(), 64);
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_integrated_scheduler_is_outside_production_prove_and_phase_aligned() {
    let production_source = include_str!("../proof/mod.rs");
    let measured_source = include_str!("../proof/main_acceptance.rs");
    let prove_start = production_source.find("fn prove_inner").unwrap();
    let prove_end = production_source[prove_start..]
        .find("\n#[cfg(test)]\nmod tests;")
        .map(|offset| prove_start + offset)
        .unwrap();
    let prove_body = &production_source[prove_start..prove_end];
    for forbidden in [
        "task8_continuation_differential_test",
        "schedule_main_acceptance_proof",
        "observe_device_memory_high_water",
        "MainAcceptanceOperation",
    ] {
        assert!(
            !prove_body.contains(forbidden),
            "production prove_inner contains test instrumentation token {forbidden}"
        );
    }

    let phases = [
        "transfer.ensure_transferred",
        "prepare_stage1_and_forward_setup",
        "schedule_forward_pass",
        "prepare_backward_handoff",
        "schedule_backward_phase",
        "schedule_whir_phase",
        "schedule_terminal_proof_assembly",
        "backward_keepalive.release_device_buffers",
        "GpuGKRProofJob {",
    ];
    for source in [prove_body, measured_source] {
        let mut previous = 0usize;
        for phase in phases {
            let position = source.find(phase).unwrap_or_else(|| {
                panic!("scheduler source is missing the production phase {phase}")
            });
            assert!(position >= previous, "scheduler phase {phase} is reordered");
            previous = position;
        }
    }
    assert_eq!(
        measured_source
            .matches("observe_device_memory_high_water")
            .count(),
        1,
        "the test-only scheduler must start exactly one backward observer"
    );
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_comparator_rejects_hidden_small_pool_growth() {
    let baseline = equal_task8_memory_record();
    let mut new = paired_new_task8_memory_record();
    new.backward.peak_logical_live_bytes += 1;
    let error = compare_task8_exact_memory(&baseline, &new).unwrap_err();
    assert!(error.contains("backward logical_live"), "{error}");
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_comparator_rejects_whole_peak_masking() {
    let baseline = equal_task8_memory_record();
    let mut new = paired_new_task8_memory_record();
    new.backward.peak_physical_backing_bytes += 1;
    let error = compare_task8_exact_memory(&baseline, &new).unwrap_err();
    assert!(error.contains("backward physical_backing"), "{error}");
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_record_rejects_entry_config_and_return_drift() {
    let baseline = equal_task8_memory_record();
    let new = paired_new_task8_memory_record();

    let mut mutated = new.clone();
    mutated.configuration.small_allocator_pool_blocks += 1;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("configuration"));

    let mut mutated = new.clone();
    mutated.configuration.allocator_block_log_size += 1;
    mutated.configuration.actual_device_arena_bytes =
        baseline.configuration.actual_device_arena_bytes;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("configuration"));

    for (field, physical, logical) in [
        ("physical entry", true, false),
        ("logical entry", false, true),
    ] {
        let mut mutated = new.clone();
        mutated.backward.start_physical_backing_bytes += usize::from(physical);
        mutated.backward.start_logical_live_bytes += usize::from(logical);
        let error = compare_task8_exact_memory(&baseline, &mutated).unwrap_err();
        assert!(error.contains(field), "{error}");
    }

    let mut mutated = new.clone();
    mutated.whole.return_physical_backing_bytes += 1;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("physical return-to-entry"));
    let mut mutated = new;
    mutated.whole.return_logical_live_bytes += 1;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("logical return-to-entry"));

    let mut baseline = baseline;
    let mut new = paired_new_task8_memory_record();
    baseline.whole.start_logical_live_bytes += 1;
    baseline.whole.return_logical_live_bytes += 1;
    new.whole.start_logical_live_bytes += 1;
    new.whole.return_logical_live_bytes += 1;
    let error = compare_task8_exact_memory(&baseline, &new).unwrap_err();
    assert!(
        error.contains("backward logical return-to-entry mismatch"),
        "{error}"
    );
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_accepts_distinct_backward_peak_entry_and_stable_return() {
    let mut baseline = equal_task8_memory_record();
    let mut new = paired_new_task8_memory_record();
    for record in [&mut baseline, &mut new] {
        record.backward.start_physical_backing_bytes = 110;
        record.backward.start_logical_live_bytes = 100;
        record.backward.peak_physical_backing_bytes = 130;
        record.backward.peak_logical_live_bytes = 120;
        assert_eq!(record.backward.return_physical_backing_bytes, 100);
        assert_eq!(record.backward.return_logical_live_bytes, 90);
        assert_eq!(record.whole.start_physical_backing_bytes, 100);
        assert_eq!(record.whole.start_logical_live_bytes, 90);
    }
    compare_task8_exact_memory(&baseline, &new).unwrap();
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_record_rejects_pair_protocol_drift() {
    let baseline = equal_task8_memory_record();
    let new = paired_new_task8_memory_record();

    let mut mutated = new.clone();
    mutated.order_in_pair = 0;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("orientation"));

    let mut mutated = new.clone();
    mutated.sample_index = 2;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("orientation"));

    let mut mutated = new.clone();
    mutated.arm = "legacy".to_owned();
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("arm/options"));

    let mut mutated = new;
    mutated
        .runtime_operation_census
        .candidate_added_host_callbacks = 1;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("runtime operation census"));
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_nondefault_same_size_configuration_cannot_be_labeled_default() {
    let baseline = equal_task8_memory_record();
    let mut new = paired_new_task8_memory_record();
    new.configuration.allocator_block_log_size = 19;
    new.configuration.max_device_allocation_blocks_count = Some(128 << 10);
    new.configuration.actual_device_allocation_blocks_count = 128 << 10;
    new.configuration.small_allocator_log_chunk_size = Some(7);
    new.configuration.small_allocator_pool_blocks = 32;
    assert_eq!(
        new.configuration.actual_device_arena_bytes,
        baseline.configuration.actual_device_arena_bytes
    );
    assert!(compare_task8_exact_memory(&baseline, &new)
        .unwrap_err()
        .contains("configuration"));
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_exact_memory_record_is_raw_integer_bytes() {
    let json = serde_json::to_string(&equal_task8_memory_record()).unwrap();
    assert!(json.contains("peak_physical_backing_bytes"));
    assert!(json.contains("peak_logical_live_bytes"));
    assert!(json.contains("summed_requested_bytes"));
    assert!(!json.contains("GiB"));
    assert!(!json.contains("."));
}

fn assert_device_slices_equal_chunked<T>(
    label: &str,
    lhs: &era_cudart::slice::DeviceSlice<T>,
    rhs: &era_cudart::slice::DeviceSlice<T>,
    context: &ProverContext,
) where
    T: Copy + Default + PartialEq + std::fmt::Debug,
{
    assert_eq!(lhs.len(), rhs.len(), "{label} length mismatch");
    const CHUNK_BYTES: usize = 64 << 20;
    let chunk_len = (CHUNK_BYTES / std::mem::size_of::<T>()).max(1);
    let mut lhs_host = vec![T::default(); chunk_len.min(lhs.len())];
    let mut rhs_host = vec![T::default(); chunk_len.min(rhs.len())];
    for offset in (0..lhs.len()).step_by(chunk_len) {
        let len = chunk_len.min(lhs.len() - offset);
        memory_copy_async(
            &mut lhs_host[..len],
            &lhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut rhs_host[..len],
            &rhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        if lhs_host[..len] != rhs_host[..len] {
            let local = lhs_host[..len]
                .iter()
                .zip(&rhs_host[..len])
                .position(|(lhs, rhs)| lhs != rhs)
                .unwrap();
            assert_eq!(
                lhs_host[local],
                rhs_host[local],
                "{label} mismatch at element {}",
                offset + local
            );
        }
    }
}

fn run_stage1_buffer_parity(fixture: &BasicUnrolledFixture) {
    use gpu_gkr::proof_layout::GpuGKRTraceGeometry;
    use gpu_gkr::stage1::{
        generate_with_witness_strategy, GpuGKRStage1Output, WitnessGenerationStrategy,
    };

    let transfers = fixture.schedule_transfers().unwrap();
    transfers
        .transfer
        .ensure_transferred(&fixture.context)
        .unwrap();
    let setup = transfers
        .setup
        .as_ref()
        .expect("stage-1 parity fixture requires a setup transfer");
    let geometry = GpuGKRTraceGeometry {
        log_domain_size: setup.trace_holder.log_domain_size,
        log_lde_factor: setup.trace_holder.log_lde_factor,
        log_rows_per_leaf: setup.trace_holder.log_rows_per_leaf,
        log_tree_cap_size: setup.trace_holder.log_tree_cap_size,
    };
    let generate = |strategy| -> GpuGKRStage1Output {
        generate_with_witness_strategy(
            fixture.circuit_type,
            &fixture.compiled_circuit,
            geometry,
            Some(setup.trace_holder.get_hypercube_evals()),
            transfers
                .decoder
                .as_ref()
                .map(|decoder| &decoder.data_device[..]),
            transfers
                .inits_and_teardowns
                .as_ref()
                .map(|transfer| &transfer.data_device),
            transfers
                .tracing_data
                .as_ref()
                .map(|transfer| &transfer.data_device),
            None,
            &fixture.context,
            strategy,
        )
        .unwrap()
    };

    let split = generate(WitnessGenerationStrategy::Split);
    fixture.context.get_exec_stream().synchronize().unwrap();
    let fused = generate(WitnessGenerationStrategy::Fused);
    fixture.context.get_exec_stream().synchronize().unwrap();
    assert_device_slices_equal_chunked(
        "memory hypercube",
        split.memory_trace_holder.get_hypercube_evals(),
        fused.memory_trace_holder.get_hypercube_evals(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "witness hypercube",
        split.witness_trace_holder.get_hypercube_evals(),
        fused.witness_trace_holder.get_hypercube_evals(),
        &fixture.context,
    );
    match (
        split.scratch_space_for_test(),
        fused.scratch_space_for_test(),
    ) {
        (Some(split), Some(fused)) => {
            assert_device_slices_equal_chunked("scratch", split, fused, &fixture.context)
        }
        (None, None) => {}
        _ => panic!("scratch allocation presence differs"),
    }
    assert_device_slices_equal_chunked(
        "generic/decoder mappings",
        split.lookup_mappings.generic_family(),
        fused.lookup_mappings.generic_family(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "range-16 mappings",
        split.lookup_mappings.range_check_16(),
        fused.lookup_mappings.range_check_16(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "timestamp mappings",
        split.lookup_mappings.timestamp(),
        fused.lookup_mappings.timestamp(),
        &fixture.context,
    );
}

#[test]
#[ignore]
fn run_add_sub_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_basic_unrolled_profiling_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_load_store_subword_only_profiling_fixture());
}

#[test]
#[ignore]
fn run_unified_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_unified_profiling_fixture());
}

#[test]
#[ignore]
fn run_blake2_compression_delegation_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_blake2_with_compression_profiling_fixture());
}

/// Full-proof parity at Sec100, where the lookup-challenge and WHIR-batching
/// PoWs are non-zero — exercises the on-device grinding + nonce path.
#[test]
#[ignore]
fn run_add_sub_proof_parity_test_sec100() {
    run_proof_parity(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn run_add_sub_multi_schedule_test() {
    run_multi_schedule(&prepare_basic_unrolled_proof_fixture());
}

#[test]
#[ignore]
fn run_add_sub_profile_test() {
    run_profile(&prepare_basic_unrolled_profiling_fixture());
}

// ---------------------------------------------------------------------------
// jump_branch_slt fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_jump_branch_slt_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        jump_branch_slt_mod::witness_eval_fn,
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<BF>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_jump_branch_slt_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        jump_branch_slt_mod::witness_eval_fn,
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_jump_branch_slt_proof_parity_test() {
    run_proof_parity(&prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[ignore]
fn run_jump_branch_slt_multi_schedule_test() {
    run_multi_schedule(&prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[ignore]
fn run_jump_branch_slt_profile_test() {
    run_profile(&prepare_jump_branch_slt_profiling_fixture());
}

// ---------------------------------------------------------------------------
// shift_binop fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_shift_binop_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::ShiftBinary,
        SHIFT_BINOP_LAYOUT_PATH,
        shift_binop_mod::witness_eval_fn,
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BF>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_shift_binop_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::ShiftBinary,
        SHIFT_BINOP_LAYOUT_PATH,
        shift_binop_mod::witness_eval_fn,
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_shift_binop_proof_parity_test() {
    run_proof_parity(&prepare_shift_binop_proof_fixture());
}

#[test]
#[ignore]
fn run_shift_binop_multi_schedule_test() {
    run_multi_schedule(&prepare_shift_binop_proof_fixture());
}

#[test]
#[ignore]
fn run_shift_binop_profile_test() {
    run_profile(&prepare_shift_binop_profiling_fixture());
}

// ---------------------------------------------------------------------------
// mul_div fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_mul_div_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<MUL_DIV_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_mul_div_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<MUL_DIV_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_mul_div_proof_parity_test() {
    run_proof_parity(&prepare_mul_div_proof_fixture());
}

#[test]
#[ignore]
fn run_mul_div_multi_schedule_test() {
    run_multi_schedule(&prepare_mul_div_proof_fixture());
}

#[test]
#[ignore]
fn run_mul_div_profile_test() {
    run_profile(&prepare_mul_div_profiling_fixture());
}

// ---------------------------------------------------------------------------
// load_store_word_only fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_load_store_word_only_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_memory_proof_fixture::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
        MEM_WORD_ONLY_LAYOUT_PATH,
        mem_word_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(td);
            for (t, tbl) in cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_load_store_word_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_memory_proof_fixture::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
        MEM_WORD_ONLY_LAYOUT_PATH,
        mem_word_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(td);
            for (t, tbl) in cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_load_store_word_only_proof_parity_test() {
    run_proof_parity(&prepare_load_store_word_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_word_only_multi_schedule_test() {
    run_multi_schedule(&prepare_load_store_word_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_word_only_profile_test() {
    run_profile(&prepare_load_store_word_only_profiling_fixture());
}

// ---------------------------------------------------------------------------
// load_store_subword_only fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_load_store_subword_only_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) =
        prepare_unrolled_memory_proof_fixture::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(
            &[15, 1],
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
            MEM_SUBWORD_ONLY_LAYOUT_PATH,
            mem_subword_only_mod::witness_eval_fn,
            |td, binary| {
                cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(td);
                for (t, tbl) in
                    cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(binary)
                {
                    td.add_table_with_content(t, tbl);
                }
            },
            true,
        );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_load_store_subword_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_memory_proof_fixture::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        MEM_SUBWORD_ONLY_LAYOUT_PATH,
        mem_subword_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(td);
            for (t, tbl) in
                cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                    _,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_load_store_subword_only_proof_parity_test() {
    run_proof_parity(&prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_only_multi_schedule_test() {
    run_multi_schedule(&prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_only_profile_test() {
    run_profile(&prepare_load_store_subword_only_profiling_fixture());
}

// ===========================================================================
// DELEGATION PROOF FIXTURES
//
// These drive a delegation circuit through the GPU `prove()` path. Each replays
// from its OWN correct workload: bigint from `examples/bigint_with_control`
// (issues one bigint call), keccak from keccak_f1600, and the two blake2 variants
// from the `examples/multi_family_smoke` apps (nd `[50, 0xDEAD_BEEF]`, matching the
// CPU unified orchestration test). All four build their fixture + CPU reference +
// tracing host, then prove on the GPU.
//
// All four tests are kept `#[ignore]`d (heavy GPU) — run with `--ignored`.
// ===========================================================================

const BIGINT_DELEGATION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json";
const BIGINT_WITH_CONTROL_BINARY_PATH: &str = "examples/bigint_with_control/app.bin";
const BIGINT_WITH_CONTROL_TEXT_PATH: &str = "examples/bigint_with_control/app.text";

const BLAKE2_WITH_COMPRESSION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json";
const BLAKE2_WITH_COMPRESSION_BINARY_PATH: &str =
    "examples/multi_family_smoke/app_blake2_with_compression.bin";
const BLAKE2_WITH_COMPRESSION_TEXT_PATH: &str =
    "examples/multi_family_smoke/app_blake2_with_compression.text";
const BLAKE2_WITH_COMPRESSION_ND: [u32; 2] = [50, 0xDEAD_BEEF];
const BLAKE2_NUM_DELEGATION_CYCLES: usize = 1 << 20;

const BLAKE2_G_FUNCTION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/blake2_g_function_layout_gkr.json";
const BLAKE2_G_FUNCTION_BINARY_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.bin";
const BLAKE2_G_FUNCTION_TEXT_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.text";
const BLAKE2_G_FUNCTION_ND: [u32; 2] = [50, 0xDEAD_BEEF];
const BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;

/// Replays `examples/bigint_with_control` (a program that issues exactly one
/// bigint delegation call via the bigint CSR ABI; it takes no non-determinism
/// input, so the nd array below is unused padding), so `bigint_calls > 0` and
/// the fixture drives a REAL bigint delegation proof.
fn replay_bigint_delegation_buffer() -> (Vec<BigintDelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer_for_workload::<_, FullUnsignedMachineDecoderConfig>(
        BIGINT_WITH_CONTROL_BINARY_PATH,
        BIGINT_WITH_CONTROL_TEXT_PATH,
        &[15, 1],
        false,
        |counters| counters.bigint_calls,
        BigintDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
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
    assert!(
        !buffer.is_empty(),
        "examples/bigint_with_control must exercise the bigint delegation \
         (bigint_calls == 0) — the workload assumption is wrong",
    );
    eprintln!("bigint delegation: bigint_calls = {}", buffer.len());

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_bigint_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_bigint_delegation_buffer();
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    // The oracle borrows `buffer`; `prepare_delegation_proof_fixture` consumes
    // the buffer only after building the CPU reference (which is what uses the
    // oracle), so clone the buffer for the tracing host.
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::BigIntWithControl,
        BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

fn prepare_bigint_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_bigint_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::BigIntWithControl,
        BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer,
        1 << 22,
    )
}

/// bigint delegation proof_parity: GPU proof == CPU reference, byte-identical.
/// `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_bigint_proof_parity_test() {
    run_proof_parity(&prepare_bigint_proof_fixture());
}

#[test]
#[ignore]
fn run_bigint_multi_schedule_test() {
    run_multi_schedule(&prepare_bigint_proof_fixture());
}

#[test]
#[ignore]
fn run_bigint_profile_test() {
    run_profile(&prepare_bigint_profiling_fixture());
}

// ---------------------------------------------------------------------------
// keccak_special5 delegation fixture wrappers + test functions
//
// keccak_f1600 exercises the keccak delegation (`keccak_calls > 0`); the GPU
// delegation proof is verified byte-equal to the CPU reference — see the section
// banner above.
// ---------------------------------------------------------------------------

const KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/keccak_special5_layout_gkr.json";

/// Replay the keccak_special5 delegation witness buffer from the keccak_f1600
/// workload. Asserts `keccak_calls > 0` (an empty delegation produces no proof)
/// BEFORE the caller reaches the expensive GPU build.
fn replay_keccak_special5_delegation_buffer(
) -> (Vec<KeccakSpecial5DelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer(
        false,
        |counters| counters.keccak_calls,
        KeccakSpecial5DelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
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
    assert!(
        !buffer.is_empty(),
        "keccak_f1600 workload must exercise the keccak delegation (keccak_calls > 0); \
         got an empty buffer — the workload assumption is wrong",
    );
    eprintln!("keccak delegation: keccak_calls = {}", buffer.len());

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_keccak_special5_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_keccak_special5_delegation_buffer();
    let oracle = KeccakDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::KeccakSpecial5,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::keccak_special5_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

fn prepare_keccak_special5_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_keccak_special5_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::KeccakSpecial5,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer,
        1 << 22,
    )
}

/// keccak_special5 delegation proof_parity: GPU proof == CPU reference,
/// byte-identical. `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_keccak_special5_proof_parity_test() {
    run_proof_parity(&prepare_keccak_special5_proof_fixture());
}

#[test]
#[ignore]
fn run_keccak_special5_multi_schedule_test() {
    run_multi_schedule(&prepare_keccak_special5_proof_fixture());
}

#[test]
#[ignore]
fn run_keccak_special5_profile_test() {
    run_profile(&prepare_keccak_special5_profiling_fixture());
}

// ---------------------------------------------------------------------------
// blake2_with_compression delegation fixture wrappers + test functions
//
// Replays from `examples/multi_family_smoke/app_blake2_with_compression` with
// nd `[50, 0xDEAD_BEEF]` (the same program + inputs the CPU unified
// orchestration test's `multi_family_smoke_blake_compression` config uses),
// which exercises the blake2 round-function (compression) delegation
// (`blake_calls > 0`). GPU↔CPU proof parity is verified byte-identical — see the
// section banner above.
// ---------------------------------------------------------------------------

/// The oracle/witness types this delegation needs, imported directly (test-only
/// exemption from the upstream-only-import rule): `Blake2sGFunctionDelegationOracle`
/// is not re-exported by `crate::upstream` (only the round-function/bigint/keccak
/// oracles are), and `Blake2sGFunctionDelegationWitness` lives one level deeper
/// than the `mod.rs`-level `witness::` imports reach.
use prover::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::BlakeGFunctionDelegationDestinationHolder;

/// Replay the blake2_with_extended_control (compression) delegation witness
/// buffer from the `app_blake2_with_compression` workload. Asserts
/// `blake_calls > 0` BEFORE the caller reaches the expensive GPU build.
fn replay_blake2_with_compression_delegation_buffer(
) -> (Vec<Blake2sRoundFunctionDelegationWitness>, TableDriver<BF>) {
    // multi_family_smoke is a reduced-machine program; it uses the
    // special-opcode extension only the reduced decoder knows.
    let buffer = replay_delegation_trace_buffer_for_workload::<_, ReducedMachineDecoderConfig>(
        BLAKE2_WITH_COMPRESSION_BINARY_PATH,
        BLAKE2_WITH_COMPRESSION_TEXT_PATH,
        &BLAKE2_WITH_COMPRESSION_ND,
        false,
        |counters| counters.blake_calls,
        Blake2sRoundFunctionDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
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
    assert!(
        !buffer.is_empty(),
        "app_blake2_with_compression workload must exercise the blake2 round-function \
         (compression) delegation (blake_calls == 0); got an empty buffer — the workload \
         assumption is wrong",
    );
    eprintln!(
        "blake2_with_compression delegation: blake_calls = {}",
        buffer.len()
    );

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_blake2_with_compression_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_blake2_with_compression_delegation_buffer();
    let oracle = Blake2sDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::Blake2WithCompression,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::blake2_with_extended_control_mod::witness_eval_fn,
        BLAKE2_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_with_compression_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_with_compression_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2WithCompression,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        &table_driver,
        buffer,
        BLAKE2_NUM_DELEGATION_CYCLES,
    )
}

/// blake2_with_compression (blake2_with_extended_control) delegation proof_parity:
/// GPU proof == CPU reference, byte-identical. `#[ignore]`d as a heavy GPU test —
/// run with `--ignored`.
#[test]
#[ignore]
fn run_blake2_with_compression_proof_parity_test() {
    run_proof_parity(&prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_multi_schedule_test() {
    run_multi_schedule(&prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_profile_test() {
    run_profile(&prepare_blake2_with_compression_profiling_fixture());
}

// ---------------------------------------------------------------------------
// blake2_g_function delegation fixture wrappers + test functions
//
// Replays from `examples/multi_family_smoke/app_blake2_g_function` with nd
// `[50, 0xDEAD_BEEF]` (the same program + inputs the CPU unified
// orchestration test's `multi_family_smoke_blake_g_function` config uses,
// and the default workload `prepare_unified_proof_fixture` already drives),
// which exercises the blake2 G-function delegation
// (`blake_g_function_calls > 0`). GPU proof == CPU reference, byte-identical
// (see the section banner). `#[ignore]`d as a heavy GPU test — run with `--ignored`.
// ---------------------------------------------------------------------------

/// Replay the blake2_g_function delegation witness buffer from the
/// `app_blake2_g_function` workload. Asserts `blake_g_function_calls > 0`
/// BEFORE the caller reaches the expensive GPU build.
fn replay_blake2_g_function_delegation_buffer(
) -> (Vec<Blake2sGFunctionDelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer_for_workload::<_, ReducedMachineDecoderConfig>(
        BLAKE2_G_FUNCTION_BINARY_PATH,
        BLAKE2_G_FUNCTION_TEXT_PATH,
        &BLAKE2_G_FUNCTION_ND,
        false,
        |counters| counters.blake_g_function_calls,
        Blake2sGFunctionDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
            let mut tracer = BlakeGFunctionDelegationDestinationHolder {
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
    assert!(
        !buffer.is_empty(),
        "app_blake2_g_function workload must exercise the blake2 G-function delegation \
         (blake_g_function_calls == 0); got an empty buffer — the workload assumption is wrong",
    );
    eprintln!(
        "blake2_g_function delegation: blake_g_function_calls = {}",
        buffer.len()
    );

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::blake2_g_function::blake2_g_function_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_blake2_g_function_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_blake2_g_function_delegation_buffer();
    let oracle = Blake2sGFunctionDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::Blake2GFunction,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::blake2_g_function_mod::witness_eval_fn,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_g_function_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_g_function_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2GFunction,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        &table_driver,
        buffer,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    )
}

/// blake2_g_function delegation proof_parity. The GPU proof is
/// byte-identical to the CPU reference (blake_g_function_calls = 80). `#[ignore]`d
/// only because it is a heavy GPU test.
#[test]
#[ignore]
fn run_blake2_g_function_proof_parity_test() {
    run_proof_parity(&prepare_blake2_g_function_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_g_function_multi_schedule_test() {
    run_multi_schedule(&prepare_blake2_g_function_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_g_function_profile_test() {
    run_profile(&prepare_blake2_g_function_profiling_fixture());
}

// ---------------------------------------------------------------------------
// unified multi_schedule (with closure-to-ONE grand-product assertions)
// ---------------------------------------------------------------------------

#[test]
#[ignore]
fn run_unified_proof_parity_test() {
    run_proof_parity(&prepare_unified_proof_fixture());
}

/// Full e2e unified proof parity + closure-to-ONE.
///
/// Proves the unified_reduced_machine circuit on the GPU and asserts the proof is
/// field-wise bit-exact vs the CPU `prove_configured_with_gkr` reference
/// (`assert_gkr_proof_eq_for_test` covers `grand_product_accumulator_computed` AND
/// `whir_proof` incl. PoW/queries). Then drives the no-filter grand-product
/// accumulator closure using the GPU proof's accumulator and asserts it closes to
/// `E4::ONE` — mirroring the CPU orchestration (orchestration/unified.rs:259-278).
/// This exercises the full backward and WHIR path, including base-layer cached
/// relation extras in the transcript.
///
/// Concurrent shape (schedule -> schedule -> finish -> finish), NOT serial: both
/// unified (2^24) jobs are scheduled before either finishes, so the second proof's
/// device allocations land on blocks the first proof wrote and freed (the first
/// job keeps only its input transfers alive until `finish()`, which shifts the
/// second proof's placement onto recycled, non-zero memory). This is the exact
/// condition that exposed a witness-trace uninitialized-read: the witness
/// generators write the per-opcode lookup columns only under `IF` guards, so rows
/// whose opcode doesn't match were left unwritten and read as fresh-page zeros on a
/// first proof but as stale data on the recycled second proof — diverging the
/// `Lookup16Bits`/`LookupTimestamps`/`GenericLookup` base-layer claims. The fix is
/// the codegen zero-default for conditionally-written witness columns
/// (`gpu_witness_eval_generator`); this test guards against its regression.
/// `prove()` is balanced — every device allocation it makes is released
/// stream-ordered before it returns (asserted per-prove in `schedule_prove`) — so a
/// single ~54 GiB peak fits the 64 GiB fixture arena even with both jobs live.
#[test]
#[ignore]
fn run_unified_multi_schedule_test() {
    let fixture = prepare_unified_proof_fixture();
    let baseline_device_usage = fixture.base.context.get_used_mem_current();

    // Schedule both jobs before finishing either: the second proof reuses the
    // first's freed (written) device blocks, exercising the cross-proof recycling
    // path that surfaced the uninitialized-witness read.
    let proof_job_0 = fixture.schedule_prove().unwrap();
    let proof_job_1 = fixture.schedule_prove().unwrap();

    let (gpu_proof_0, proof_time_ms_0) = proof_job_0.finish().unwrap();
    eprintln!("unified proof_job_0 proof time: {proof_time_ms_0} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_0, &fixture.expected_cpu_proof);

    // No-filter grand-product accumulator closure, driven by the GPU proof's
    // `grand_product_accumulator_computed` (proven == CPU above). Closing to ONE
    // confirms the GPU path produces a sound full-machine permutation argument.
    let mut acc = produce_initial_permutation_product_contribution::<BF, E4>(
        &fixture.base.unified_register_final_state,
        INITIAL_PC,
        split_timestamp(INITIAL_TIMESTAMP),
        fixture.base.unified_final_pc,
        split_timestamp(fixture.base.unified_final_timestamp),
        &fixture.base.external_challenges,
    );
    acc.mul_assign(&gpu_proof_0.grand_product_accumulator_computed);
    for factor in fixture.base.delegation_grand_product_factors.iter() {
        acc.mul_assign(factor);
    }
    assert_eq!(
        acc,
        E4::ONE,
        "unified grand-product accumulator must close to ONE"
    );
    drop(gpu_proof_0);

    // The concurrently-scheduled second proof must be bit-exact too (this is the
    // one that ran on recycled blocks) and device memory must return to baseline.
    let (gpu_proof_1, proof_time_ms_1) = proof_job_1.finish().unwrap();
    eprintln!("unified proof_job_1 proof time: {proof_time_ms_1} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_1, &fixture.expected_cpu_proof);
    drop(gpu_proof_1);

    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline_device_usage,
        "device memory must return to baseline after both proofs complete"
    );
}

/// Unified circuit profile run (warmup + profiled prove, structure check only).
/// Uses a no-CPU-reference fixture so it skips the expensive CPU unified prove.
#[test]
#[ignore]
fn run_unified_profile_test() {
    run_profile(&prepare_unified_profiling_fixture());
}

// ---------------------------------------------------------------------------
// inits_and_teardowns fixture wrappers + test functions
//
// The standalone i/t circuit is memory-only (zero-width setup, no per-cycle
// witness); its `BasicUnrolledFixture` is built in the `inits_and_teardowns`
// module (setup = None, empty tracing host, i/t trace host = Some). It is
// still driven through the same three matrix bodies as every other circuit.
// ---------------------------------------------------------------------------

fn prepare_inits_and_teardowns_matrix_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_inits_and_teardowns_matrix_profiling_fixture() -> BasicUnrolledFixture {
    super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(false).0
}

// Regression guards for zero-width base-layer handling (width-0 witness):
// initial transcript cap gating and WHIR base-cap gating.
#[test]
#[ignore]
fn run_inits_and_teardowns_proof_parity_test() {
    run_proof_parity(&prepare_inits_and_teardowns_matrix_proof_fixture());
}

#[test]
#[ignore]
fn run_inits_and_teardowns_multi_schedule_test() {
    run_multi_schedule(&prepare_inits_and_teardowns_matrix_proof_fixture());
}

// run_profile checks proof structure + peak memory only (no CPU comparison),
// unlike the other two.
#[test]
#[ignore]
fn run_inits_and_teardowns_profile_test() {
    run_profile(&prepare_inits_and_teardowns_matrix_profiling_fixture());
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_integrated_fixture_builders() -> [(&'static str, fn() -> BasicUnrolledFixture); 12] {
    [
        ("basic", prepare_basic_unrolled_profiling_fixture),
        ("jump_branch_slt", prepare_jump_branch_slt_profiling_fixture),
        ("shift_binop", prepare_shift_binop_profiling_fixture),
        ("mul_div", prepare_mul_div_profiling_fixture),
        (
            "load_store_word",
            prepare_load_store_word_only_profiling_fixture,
        ),
        (
            "load_store_subword",
            prepare_load_store_subword_only_profiling_fixture,
        ),
        ("bigint", prepare_bigint_profiling_fixture),
        ("keccak_special5", prepare_keccak_special5_profiling_fixture),
        (
            "blake2_compression",
            prepare_blake2_with_compression_profiling_fixture,
        ),
        ("blake2_g", prepare_blake2_g_function_profiling_fixture),
        ("unified", prepare_unified_profiling_fixture),
        (
            "inits_and_teardowns",
            prepare_inits_and_teardowns_matrix_profiling_fixture,
        ),
    ]
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8IntegratedArm {
    Legacy,
    Production,
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
impl Task8IntegratedArm {
    fn label(self) -> &'static str {
        match self {
            Self::Legacy => "legacy",
            Self::Production => "production",
        }
    }

    fn options(self) -> GkrBackwardOptions {
        match self {
            Self::Legacy => GkrBackwardOptions {
                windowed_r0: false,
                windowed_main_continuations: false,
                ..GkrBackwardOptions::default()
            },
            Self::Production => GkrBackwardOptions {
                windowed_r0: true,
                windowed_main_continuations: true,
                ..GkrBackwardOptions::default()
            },
        }
    }
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
struct Task8IntegratedBinding {
    artifact_head: String,
    artifact_tree: String,
    release_executable: String,
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
impl Task8IntegratedBinding {
    fn from_environment() -> Self {
        let read = |key: &str| {
            std::env::var(key).unwrap_or_else(|_| panic!("missing required packet binding {key}"))
        };
        Self {
            artifact_head: read("BLUE_MAIN_AB_ARTIFACT_HEAD"),
            artifact_tree: read("BLUE_MAIN_AB_ARTIFACT_TREE"),
            release_executable: read("BLUE_MAIN_AB_RELEASE_EXECUTABLE"),
        }
    }
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_allocator_configuration(
    fixture: &BasicUnrolledFixture,
    configured: Task8ConfiguredContext,
) -> Task8AllocatorConfiguration {
    let config = configured.config;
    let actual_device_arena_bytes = fixture.context.get_mem_size();
    assert_eq!(
        actual_device_arena_bytes % (1usize << config.allocator_block_log_size),
        0
    );
    Task8AllocatorConfiguration {
        powers_of_w_coarse_log_count: config.powers_of_w_coarse_log_count,
        allocator_block_log_size: config.allocator_block_log_size,
        device_slack_static_bytes: config.device_slack_static_bytes,
        device_slack_per_thread_bytes: config.device_slack_per_thread_bytes,
        max_device_allocation_blocks_count: config.max_device_allocation_blocks_count,
        host_allocator_block_log_size: config.host_allocator_block_log_size,
        host_allocator_blocks_count: config.host_allocator_blocks_count,
        actual_device_allocation_blocks_count: actual_device_arena_bytes
            >> config.allocator_block_log_size,
        actual_device_arena_bytes,
        small_allocator_enabled: config.small_allocator_log_chunk_size.is_some(),
        small_allocator_log_chunk_size: config.small_allocator_log_chunk_size,
        small_allocator_pool_blocks: config.small_allocator_pool_blocks,
    }
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_assert_peak_snapshot(
    label: &str,
    snapshot: gpu_prover_context::PoolMemoryHighWaterSnapshot,
    report: gpu_prover_context::PoolMemoryHighWaterReport,
) {
    assert_eq!(
        snapshot.start, report.start,
        "{label} start changed after seal"
    );
    assert_eq!(
        snapshot.physical_backing_peak_bytes, report.physical_backing_peak_bytes,
        "{label} physical peak changed after seal"
    );
    assert_eq!(
        snapshot.logical_live_peak_bytes, report.logical_live_peak_bytes,
        "{label} logical peak changed after seal"
    );
    assert_eq!(
        snapshot.summed_requested_bytes, report.summed_requested_bytes,
        "{label} requested bytes changed after seal"
    );
    assert_eq!(
        snapshot.peak_window_end, report.peak_window_end,
        "{label} peak-window end changed after seal"
    );
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_run_integrated_sample(
    fixture: &BasicUnrolledFixture,
    configuration: Task8AllocatorConfiguration,
    binding: &Task8IntegratedBinding,
    workload_id: &str,
    arm: Task8IntegratedArm,
    sample_index: usize,
    pair_index: usize,
    order_in_pair: usize,
) -> (Task8ExactMemoryRecord, Vec<u8>) {
    let options = arm.options();
    let selected_strategy = crate::proof::resolve_backward_execution_strategy(
        &fixture.gkr_programs,
        &fixture.prover_config,
        options,
    );
    match arm {
        Task8IntegratedArm::Legacy => {
            assert_eq!(
                selected_strategy,
                gpu_gkr::BackwardExecutionStrategy::PerRound
            )
        }
        Task8IntegratedArm::Production => {
            assert_eq!(
                selected_strategy,
                gpu_gkr::BackwardExecutionStrategy::WindowedR0
            )
        }
    }
    let output = fixture
        .schedule_exact_memory(options)
        .unwrap()
        .finish()
        .unwrap();
    task8_assert_peak_snapshot("backward", output.backward_peak_window, output.backward);
    task8_assert_peak_snapshot("whole", output.whole_peak_window, output.whole);
    assert_eq!(output.operations, expected_task8_operation_trace());
    assert_gkr_proof_structure_for_test(&output.proof, &fixture.prover_config.whir_schedule);

    let proof_bytes = canonical_serialized_bytes_for_test(&output.proof);
    let main_folding_steps = fixture
        .gkr_programs
        .compiled_circuit()
        .trace_len
        .trailing_zeros() as usize;
    let main_layer_count = fixture.gkr_programs.compiled_circuit().layers.len();
    assert!(
        main_layer_count > 0,
        "the integrated fixture must contain MAIN layers"
    );
    let windows_per_layer =
        gpu_gkr::main_continuation_window_count(options, selected_strategy, main_folding_steps)
            .unwrap() as usize;
    let production = arm == Task8IntegratedArm::Production;
    let record = Task8ExactMemoryRecord {
        schema_version: 2,
        harness_contract: "main-integrated-production-vs-whole-legacy-v1".to_owned(),
        artifact_head: binding.artifact_head.clone(),
        artifact_tree: binding.artifact_tree.clone(),
        release_executable: binding.release_executable.clone(),
        workload_id: workload_id.to_owned(),
        sample_index,
        pair_index,
        order_in_pair,
        arm: arm.label().to_owned(),
        backward_options: format!("{options:?}"),
        final_trace_size_log_2: fixture.final_trace_size_log_2,
        configuration,
        backward: output.backward.into(),
        whole: output.whole.into(),
        proof_blake2s: task8_blake2s_digest(&proof_bytes),
        proof_serialized_bytes: proof_bytes.len(),
        proof_time_ms_bits: output.proof_time_ms.to_bits(),
        selected_strategy: format!("{selected_strategy:?}"),
        main_folding_steps,
        main_layer_count,
        main_r0_launch_count: usize::from(production) * main_layer_count,
        main_continuation_planned_window_count: windows_per_layer * main_layer_count,
        main_tail_launch_count: usize::from(production) * main_layer_count,
        legacy_layer_count: usize::from(!production) * main_layer_count,
        legacy_round_count: usize::from(!production) * main_layer_count * main_folding_steps,
        operation_trace: output.operations,
        runtime_operation_census: Task8RuntimeOperationCensus {
            initial_input_h2d: 1,
            final_slab_d2h: 1,
            proof_assembly_after_final_d2h: 1,
            candidate_added_h2d: 0,
            candidate_added_d2h: 0,
            candidate_added_host_callbacks: 0,
            candidate_added_host_staging: 0,
            candidate_added_host_computation: 0,
        },
    };
    (record, proof_bytes)
}

/// Production-shaped, same-binary MAIN acceptance harness.
///
/// This selector is intentionally ignored and may run only through the frozen
/// packet. It performs two excluded warmups (legacy then production) followed
/// by six counterbalanced pairs (`A,B,B,A` repeated three times) for every one
/// of the twelve production fixture families.
#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
#[test]
#[ignore]
fn main_integrated_production_vs_whole_layer_legacy_gpu_acceptance() {
    let binding = Task8IntegratedBinding::from_environment();
    let mut measured_rows = 0usize;
    let mut measured_pairs = 0usize;
    let mut production_windows = 0usize;
    for (workload_id, build_fixture) in task8_integrated_fixture_builders() {
        let fixture = build_fixture();
        let configuration =
            task8_allocator_configuration(&fixture, take_task8_configured_context());

        for arm in [Task8IntegratedArm::Legacy, Task8IntegratedArm::Production] {
            let (_warmup, proof_bytes) = task8_run_integrated_sample(
                &fixture,
                configuration,
                &binding,
                workload_id,
                arm,
                usize::MAX,
                usize::MAX,
                usize::MAX,
            );
            assert!(!proof_bytes.is_empty(), "warmup proof must be materialized");
        }

        let sequence = [
            Task8IntegratedArm::Legacy,
            Task8IntegratedArm::Production,
            Task8IntegratedArm::Production,
            Task8IntegratedArm::Legacy,
        ];
        for repetition in 0..3 {
            for local_pair in 0..2 {
                let pair_index = repetition * 2 + local_pair;
                let first_arm = sequence[local_pair * 2];
                let second_arm = sequence[local_pair * 2 + 1];
                let (first, first_proof) = task8_run_integrated_sample(
                    &fixture,
                    configuration,
                    &binding,
                    workload_id,
                    first_arm,
                    pair_index * 2,
                    pair_index,
                    0,
                );
                let (second, second_proof) = task8_run_integrated_sample(
                    &fixture,
                    configuration,
                    &binding,
                    workload_id,
                    second_arm,
                    pair_index * 2 + 1,
                    pair_index,
                    1,
                );
                assert_eq!(
                    first_proof, second_proof,
                    "{workload_id} pair {pair_index} proof bytes differ"
                );
                let (legacy, production) = if first.arm == "legacy" {
                    (&first, &second)
                } else {
                    (&second, &first)
                };
                compare_task8_exact_memory(legacy, production).unwrap();
                production_windows += production.main_continuation_planned_window_count;
                eprintln!(
                    "MAIN_INTEGRATED_AB_ROW {}",
                    serde_json::to_string(&first).unwrap()
                );
                eprintln!(
                    "MAIN_INTEGRATED_AB_ROW {}",
                    serde_json::to_string(&second).unwrap()
                );
                measured_rows += 2;
                measured_pairs += 1;
            }
        }
    }
    assert_eq!(measured_pairs, 12 * 6);
    assert_eq!(measured_rows, 12 * 12);
    assert!(
        production_windows > 0,
        "production continuation coverage is zero"
    );
    eprintln!(
        "MAIN_INTEGRATED_AB_CENSUS {}",
        serde_json::json!({
            "layouts": 12,
            "warmups": 24,
            "measured_pairs": measured_pairs,
            "measured_rows": measured_rows,
            "production_continuation_windows": production_windows,
            "selected": 1,
            "executed": 1,
            "passed": 1,
        })
    );
}
