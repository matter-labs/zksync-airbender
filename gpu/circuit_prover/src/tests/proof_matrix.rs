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
impl Task8AllocatorConfiguration {
    fn from_fixture(fixture: &BasicUnrolledFixture, configured: Task8ConfiguredContext) -> Self {
        let config = configured.config;
        let arena_bytes = fixture.context.get_mem_size();
        let block_bytes = 1usize << config.allocator_block_log_size;
        assert_eq!(arena_bytes, 64usize << 30);
        assert_eq!(arena_bytes % block_bytes, 0);
        assert_eq!(
            config.max_device_allocation_blocks_count,
            Some(arena_bytes / block_bytes),
            "Task 8 context construction silently changed the requested arena block count"
        );
        Self {
            powers_of_w_coarse_log_count: config.powers_of_w_coarse_log_count,
            allocator_block_log_size: config.allocator_block_log_size,
            device_slack_static_bytes: config.device_slack_static_bytes,
            device_slack_per_thread_bytes: config.device_slack_per_thread_bytes,
            max_device_allocation_blocks_count: config.max_device_allocation_blocks_count,
            host_allocator_block_log_size: config.host_allocator_block_log_size,
            host_allocator_blocks_count: config.host_allocator_blocks_count,
            actual_device_allocation_blocks_count: arena_bytes / block_bytes,
            actual_device_arena_bytes: arena_bytes,
            small_allocator_enabled: config.small_allocator_log_chunk_size.is_some(),
            small_allocator_log_chunk_size: config.small_allocator_log_chunk_size,
            small_allocator_pool_blocks: config.small_allocator_pool_blocks,
        }
    }
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
struct Task8ExactMemoryRecord {
    schema_version: u32,
    performance_plan_sha256: String,
    observer_dependency_commit: String,
    observer_closure_audit_sha256: String,
    inactive_observer_evidence_hook: String,
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
    proof_sha256: String,
    proof_time_ms_bits: u32,
    selected_strategy: String,
    dr_counters_observed: bool,
    dr_bundle_final_log: Option<u32>,
    dr_prepared_layer_count: Option<usize>,
    dr_r0_launch_count: Option<usize>,
    dr_continuation_launch_count: Option<usize>,
    dr_tail_launch_count: Option<usize>,
    main_continuation_window_launch_count: usize,
    main_legacy_full_round_count: usize,
    main_legacy_remainder_round_count: usize,
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
    if baseline.schema_version != 1 || new.schema_version != 1 {
        return Err("Task 8 row has an unsupported schema version".to_owned());
    }
    if baseline.performance_plan_sha256
        != "27bb732c87371b4ed3c357f8cbe524e1ae3c285150f34cfdc2e601e4163052d8"
        || new.performance_plan_sha256 != baseline.performance_plan_sha256
        || baseline.observer_dependency_commit != "2e4a6d5e58a96f94991fbbb5b797c01a830e9ee0"
        || new.observer_dependency_commit != baseline.observer_dependency_commit
        || baseline.observer_closure_audit_sha256
            != "5813895a7bcd4dbb8c5e77575e868ad9925f7be264b63627794e232339be508d"
        || new.observer_closure_audit_sha256 != baseline.observer_closure_audit_sha256
        || baseline.inactive_observer_evidence_hook
            != "producer-owned release zero-allocation/unchanged-byte comparison"
        || new.inactive_observer_evidence_hook != baseline.inactive_observer_evidence_hook
    {
        return Err("Task 8 observer/performance evidence binding differs".to_owned());
    }
    if baseline.arm != "baseline"
        || new.arm != "new"
        || !baseline
            .backward_options
            .contains("windowed_main_continuations: false")
        || !new
            .backward_options
            .contains("windowed_main_continuations: true")
    {
        return Err("Task 8 paired rows have invalid arm/options labels".to_owned());
    }
    if baseline.selected_strategy != "WindowedR0" || new.selected_strategy != "WindowedR0" {
        return Err("Task 8 paired rows did not both select WindowedR0".to_owned());
    }
    for (arm, record) in [("baseline", baseline), ("new", new)] {
        let dr_fields_present = record.dr_bundle_final_log.is_some()
            && record.dr_prepared_layer_count.is_some()
            && record.dr_r0_launch_count.is_some()
            && record.dr_continuation_launch_count.is_some()
            && record.dr_tail_launch_count.is_some();
        if record.dr_counters_observed != dr_fields_present {
            return Err(format!(
                "Task 8 {arm} row misstates DR counter observation provenance"
            ));
        }
    }
    if baseline.configuration != new.configuration {
        return Err("Task 8 allocator configuration differs between arms".to_owned());
    }
    if baseline.main_continuation_window_launch_count != 0
        || baseline.main_legacy_full_round_count == 0
        || baseline.main_legacy_remainder_round_count != 0
    {
        return Err("Task 8 legacy/off row has invalid actual execution counts".to_owned());
    }
    if new.main_continuation_window_launch_count == 0
        || new.main_legacy_full_round_count != 0
        || new.main_legacy_remainder_round_count == 0
    {
        return Err("Task 8 new/on row has invalid actual execution counts".to_owned());
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
    if baseline.proof_sha256 != new.proof_sha256 {
        return Err("Task 8 paired-arm proof SHA-256 differs".to_owned());
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
    Ok(())
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
        schema_version: 1,
        performance_plan_sha256: "27bb732c87371b4ed3c357f8cbe524e1ae3c285150f34cfdc2e601e4163052d8"
            .to_owned(),
        observer_dependency_commit: "2e4a6d5e58a96f94991fbbb5b797c01a830e9ee0".to_owned(),
        observer_closure_audit_sha256:
            "5813895a7bcd4dbb8c5e77575e868ad9925f7be264b63627794e232339be508d".to_owned(),
        inactive_observer_evidence_hook:
            "producer-owned release zero-allocation/unchanged-byte comparison".to_owned(),
        artifact_head: "head".to_owned(),
        artifact_tree: "tree".to_owned(),
        release_executable: "/tmp/test-binary".to_owned(),
        workload_id: "mutation".to_owned(),
        sample_index: 0,
        pair_index: 0,
        order_in_pair: 0,
        arm: "baseline".to_owned(),
        backward_options: "GkrBackwardOptions { windowed_main_continuations: false }".to_owned(),
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
        proof_sha256: "00".repeat(32),
        proof_time_ms_bits: 0,
        selected_strategy: "WindowedR0".to_owned(),
        dr_counters_observed: false,
        dr_bundle_final_log: None,
        dr_prepared_layer_count: None,
        dr_r0_launch_count: None,
        dr_continuation_launch_count: None,
        dr_tail_launch_count: None,
        main_continuation_window_launch_count: 0,
        main_legacy_full_round_count: 1,
        main_legacy_remainder_round_count: 0,
    }
}

#[cfg(feature = "task8_continuation_differential_test")]
fn paired_new_task8_memory_record() -> Task8ExactMemoryRecord {
    let mut record = equal_task8_memory_record();
    record.arm = "new".to_owned();
    record.sample_index = 1;
    record.order_in_pair = 1;
    record.backward_options = "GkrBackwardOptions { windowed_main_continuations: true }".to_owned();
    record.main_continuation_window_launch_count = 1;
    record.main_legacy_full_round_count = 0;
    record.main_legacy_remainder_round_count = 1;
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
    mutated.arm = "baseline".to_owned();
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("arm/options"));

    let mut mutated = new;
    mutated.dr_counters_observed = true;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("DR counter observation provenance"));
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
fn task8_fixture_builders() -> [(&'static str, fn() -> BasicUnrolledFixture); 12] {
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
#[test]
#[ignore]
fn main_continuation_prepared_differential() {
    let expected_layouts = std::collections::BTreeSet::from([
        "basic",
        "jump_branch_slt",
        "shift_binop",
        "mul_div",
        "load_store_word",
        "load_store_subword",
        "bigint",
        "keccak_special5",
        "blake2_compression",
        "blake2_g",
        "unified",
        "inits_and_teardowns",
    ]);
    let expected_mutation_families = std::collections::BTreeSet::from([
        "axis-product-infinity-coefficients".to_owned(),
        "challenges".to_owned(),
        "claim".to_owned(),
        "duplicate-missing-canonical-map".to_owned(),
        "duplicate-raw-owner".to_owned(),
        "eq-prefactor".to_owned(),
        "final-boundary-repoint".to_owned(),
        "overlapping-prior-owner".to_owned(),
        "prior-publication-cell".to_owned(),
        "row-weight".to_owned(),
        "seeded-adoption-delta-3".to_owned(),
        "source-column-displacement".to_owned(),
        "stale-eq".to_owned(),
        "transcript-seed".to_owned(),
        "window-publication-lane".to_owned(),
        "zero-remainder-take".to_owned(),
    ]);
    let expected_topology_owner_kinds = std::collections::BTreeSet::from([
        "bank".to_owned(),
        "coefficients".to_owned(),
        "descriptor".to_owned(),
        "eq".to_owned(),
        "partials".to_owned(),
        "prior_publication".to_owned(),
        "production_storage".to_owned(),
        "publication".to_owned(),
        "raw_backing".to_owned(),
        "transcript_claim".to_owned(),
        "transcript_prefactor".to_owned(),
        "transcript_seed".to_owned(),
    ]);
    let mut seen_layouts = std::collections::BTreeSet::new();
    let mut layers = 0usize;
    let mut coordinates = 0usize;
    let mut non_identity_coordinates = 0usize;
    let mut folding_steps = std::collections::BTreeSet::new();
    let mut start_rounds = std::collections::BTreeSet::new();
    let mut masks = std::collections::BTreeSet::new();
    let mut max_sources = 0usize;
    let mut max_legacy_displacement = 0usize;
    let mut semantic_comparisons = 0usize;
    let mut comparator_field_coverage_checks = 0usize;
    let mut mutation_checks = 0usize;
    let mut publication_elements_compared = 0usize;
    let mut topology_coordinates = 0usize;
    let mut later_start_shared_prior_coordinates = 0usize;
    let mut multi_source_coordinates = 0usize;
    let mut capacity_overlap_rows = 0usize;
    let mut capacity_publication_bytes = Vec::new();
    let mut capacity_overlap_live_bytes = Vec::new();
    let mut capacity_overlap_owner_counts = Vec::new();
    let mut capacity_physical_peak_bytes = Vec::new();
    let mut capacity_logical_peak_bytes = Vec::new();
    let mut mutation_families = std::collections::BTreeSet::new();

    for (workload, build) in task8_fixture_builders() {
        assert!(
            seen_layouts.insert(workload),
            "duplicate Task 8 layout {workload}"
        );
        let fixture = build();
        let _configured = take_task8_configured_context();
        let (proof, report, proof_time_ms) = fixture
            .schedule_main_continuation_differential()
            .unwrap()
            .finish()
            .unwrap();
        assert_gkr_proof_structure_for_test(&proof, &fixture.prover_config.whir_schedule);
        eprintln!(
            "Task 8 prepared differential workload={workload} layers={} comparisons={} mutations={} proof_ms={proof_time_ms}",
            report.layers, report.semantic_comparisons, report.mutation_checks
        );
        assert_eq!(report.coordinates, report.layers, "{workload}");
        assert!(report.non_identity_coordinates <= report.coordinates);
        assert_eq!(
            report.topology_coordinates,
            report.layers * report.start_rounds.len(),
            "{workload}"
        );
        assert_eq!(
            report.arm_memory_comparisons,
            2 * report.topology_coordinates,
            "{workload}"
        );
        let later_coordinates = report.topology_coordinates - report.layers;
        assert_eq!(
            report.later_start_shared_prior_coordinates, later_coordinates,
            "{workload}"
        );
        assert_eq!(
            report.source_table_identity_rows, report.layers,
            "{workload}"
        );
        assert_eq!(
            report.allocation_records,
            17 * report.topology_coordinates + 2 * later_coordinates,
            "{workload}"
        );
        assert_eq!(
            report.mutation_checks,
            16 * report.layers + 22 * later_coordinates + 2 * report.multi_source_coordinates,
            "{workload}"
        );
        assert_eq!(
            report.comparator_field_coverage_checks,
            24 * report.topology_coordinates,
            "{workload}"
        );
        assert_eq!(
            report.semantic_comparisons,
            report.publication_elements_compared + 26 * report.topology_coordinates,
            "{workload}"
        );
        assert_eq!(report.capacity_overlap_rows, report.layers, "{workload}");
        assert!(report.source_identity_records >= 2 * report.topology_coordinates);
        assert_eq!(report.source_identity_records % 2, 0);
        assert_eq!(report.source_id_census.len(), report.layers, "{workload}");
        assert_eq!(
            report.source_backing_census.len(),
            report.layers,
            "{workload}"
        );
        assert!(report.source_id_census.iter().enumerate().all(
            |(layer, (actual_layer, sources))| {
                layer == *actual_layer
                    && !sources.is_empty()
                    && sources
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                        == sources.len()
            }
        ));
        let raw_sources: usize = report
            .source_id_census
            .iter()
            .map(|(_, sources)| sources.len())
            .sum();
        let expected_program_sources: usize = fixture
            .gkr_programs
            .resolve_main_continuation_window_programs()
            .expect("Task 8 selector fixture must retain its continuation bundle")
            .layers
            .iter()
            .map(|program| program.sources.len())
            .sum();
        assert_eq!(
            report.procedural_source_records,
            expected_program_sources - raw_sources,
            "{workload}"
        );
        let folding_steps_for_capacity =
            fixture.compiled_circuit.trace_len.trailing_zeros() as usize;
        let expected_heavy_layers: Vec<_> = fixture
            .gkr_programs
            .resolve_main_continuation_window_programs()
            .expect("Task 8 selector fixture must retain its continuation bundle")
            .layers
            .iter()
            .enumerate()
            .filter_map(|(layer, program)| {
                let publication_bytes = program.sources.len()
                    * (1usize << (folding_steps_for_capacity - 3))
                    * std::mem::size_of::<E4>();
                (publication_bytes > 2usize << 30).then_some(layer)
            })
            .collect();
        assert_eq!(
            report.capacity_heavy_layers, expected_heavy_layers,
            "{workload}"
        );
        assert_eq!(
            report.source_identity_records,
            2 * report.start_rounds.len() * raw_sources,
            "{workload}"
        );
        let backing_owners: usize = report
            .source_backing_census
            .iter()
            .map(|(_, backings)| 1 + backings)
            .sum();
        assert_eq!(
            report.topology_owner_records,
            report.allocation_records + 2 * report.start_rounds.len() * backing_owners,
            "{workload}"
        );
        assert_eq!(
            report
                .topology_owner_kinds
                .iter()
                .cloned()
                .collect::<std::collections::BTreeSet<_>>(),
            expected_topology_owner_kinds,
            "{workload}"
        );
        assert_eq!(
            report
                .mutation_families
                .iter()
                .cloned()
                .collect::<std::collections::BTreeSet<_>>(),
            expected_mutation_families,
            "{workload}"
        );
        assert_eq!(
            report.capacity_publication_bytes.len(),
            report.capacity_heavy_layers.len(),
            "{workload}"
        );
        assert_eq!(
            report.capacity_publication_bytes.len(),
            report.capacity_overlap_live_bytes.len(),
            "{workload}"
        );
        assert_eq!(
            report.capacity_publication_bytes.len(),
            report.capacity_overlap_owner_counts.len(),
            "{workload}"
        );
        assert_eq!(
            report.capacity_publication_bytes.len(),
            report.capacity_physical_peak_bytes.len(),
            "{workload}"
        );
        assert_eq!(
            report.capacity_publication_bytes.len(),
            report.capacity_logical_peak_bytes.len(),
            "{workload}"
        );
        for ((((publication, overlap), owners), physical), logical) in report
            .capacity_publication_bytes
            .iter()
            .zip(&report.capacity_overlap_live_bytes)
            .zip(&report.capacity_overlap_owner_counts)
            .zip(&report.capacity_physical_peak_bytes)
            .zip(&report.capacity_logical_peak_bytes)
        {
            assert!(*publication > 2usize << 30, "{workload}");
            assert_eq!(*owners, 2, "{workload}");
            assert_eq!(*overlap, *publication + *publication / 2, "{workload}");
            assert!(*physical > 2usize << 30, "{workload}");
            assert!(*logical > 2usize << 30, "{workload}");
        }
        layers += report.layers;
        coordinates += report.coordinates;
        non_identity_coordinates += report.non_identity_coordinates;
        folding_steps.extend(report.folding_steps);
        start_rounds.extend(report.start_rounds);
        masks.extend(report.masks);
        max_sources = max_sources.max(report.max_sources);
        max_legacy_displacement = max_legacy_displacement.max(report.max_legacy_displacement);
        semantic_comparisons += report.semantic_comparisons;
        comparator_field_coverage_checks += report.comparator_field_coverage_checks;
        mutation_checks += report.mutation_checks;
        publication_elements_compared += report.publication_elements_compared;
        topology_coordinates += report.topology_coordinates;
        later_start_shared_prior_coordinates += report.later_start_shared_prior_coordinates;
        multi_source_coordinates += report.multi_source_coordinates;
        capacity_overlap_rows += report.capacity_overlap_rows;
        capacity_publication_bytes.extend(report.capacity_publication_bytes);
        capacity_overlap_live_bytes.extend(report.capacity_overlap_live_bytes);
        capacity_overlap_owner_counts.extend(report.capacity_overlap_owner_counts);
        capacity_physical_peak_bytes.extend(report.capacity_physical_peak_bytes);
        capacity_logical_peak_bytes.extend(report.capacity_logical_peak_bytes);
        mutation_families.extend(report.mutation_families);
    }

    assert_eq!(seen_layouts, expected_layouts);
    assert_eq!(layers, 57);
    assert_eq!(coordinates, 57);
    assert_eq!(non_identity_coordinates, 23);
    assert_eq!(
        folding_steps,
        std::collections::BTreeSet::from([20, 22, 23, 24])
    );
    assert_eq!(
        start_rounds,
        std::collections::BTreeSet::from([3, 6, 9, 12, 15, 18])
    );
    assert_eq!(
        masks,
        std::collections::BTreeSet::from([0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f])
    );
    assert_eq!(max_sources, 1_012);
    assert_eq!(max_legacy_displacement, 174);
    assert_eq!(capacity_overlap_rows, 57);
    assert_eq!(capacity_publication_bytes.len(), 4);
    assert_eq!(capacity_overlap_live_bytes.len(), 4);
    assert_eq!(capacity_overlap_owner_counts, vec![2; 4]);
    assert_eq!(capacity_physical_peak_bytes.len(), 4);
    assert_eq!(capacity_logical_peak_bytes.len(), 4);
    assert_eq!(mutation_families, expected_mutation_families);
    assert_eq!(
        semantic_comparisons,
        publication_elements_compared + 26 * topology_coordinates
    );
    assert_eq!(comparator_field_coverage_checks, 24 * topology_coordinates);
    assert_eq!(topology_coordinates, 342);
    assert_eq!(
        mutation_checks,
        16 * layers + 22 * later_start_shared_prior_coordinates + 2 * multi_source_coordinates
    );
    assert!(publication_elements_compared > 0);
    let census_starts: Vec<_> = start_rounds.iter().copied().collect();
    eprintln!(
        "TASK8_CENSUS_JSON={{\"layouts\":{},\"layers\":{},\"coordinates\":{},\"starts\":{:?},\"topology_coordinates\":{},\"non_identity_coordinates\":{}}}",
        seen_layouts.len(),
        layers,
        coordinates,
        census_starts,
        topology_coordinates,
        non_identity_coordinates,
    );
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_artifact_identity() -> (String, String, String) {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let rev_parse = |revision: &str| {
        let output = std::process::Command::new("git")
            .arg("-C")
            .arg(&repository)
            .arg("rev-parse")
            .arg(revision)
            .output()
            .expect("Task 8 memory review requires git for artifact provenance");
        assert!(output.status.success(), "Task 8 git rev-parse failed");
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    };
    (
        rev_parse("HEAD"),
        rev_parse("HEAD^{tree}"),
        std::env::current_exe()
            .expect("Task 8 memory review requires its executable path")
            .display()
            .to_string(),
    )
}

#[cfg(feature = "task8_continuation_differential_test")]
fn task8_sha256_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write;

    let digest = ring::digest::digest(&ring::digest::SHA256, bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest.as_ref() {
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    assert_eq!(encoded.len(), 64);
    encoded
}

#[cfg(feature = "task8_continuation_differential_test")]
#[test]
fn cpu_task8_sha256_matches_known_vector() {
    assert_eq!(
        task8_sha256_bytes(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
fn task8_proof_sha256(proof: &GKRProof<BF, E4, DefaultTreeConstructor>) -> String {
    task8_sha256_bytes(&serde_json::to_vec_pretty(proof).unwrap())
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
#[allow(clippy::too_many_arguments)]
fn task8_memory_record(
    workload: &str,
    sample_index: usize,
    pair_index: usize,
    order_in_pair: usize,
    arm: &str,
    options: GkrBackwardOptions,
    configuration: Task8AllocatorConfiguration,
    artifact: &(String, String, String),
    fixture: &BasicUnrolledFixture,
    output: Task8ExactMemoryOutput,
) -> Task8ExactMemoryRecord {
    assert_gkr_proof_structure_for_test(&output.proof, &fixture.prover_config.whir_schedule);
    let strategy = crate::proof::resolve_backward_execution_strategy(
        &fixture.gkr_programs,
        &fixture.prover_config,
        options,
    );
    assert_eq!(strategy, gpu_gkr::BackwardExecutionStrategy::WindowedR0);
    let folding_steps = fixture.compiled_circuit.trace_len.trailing_zeros() as usize;
    let layers = fixture.compiled_circuit.layers.len();
    let windows_per_layer = usize::from(
        gpu_gkr::main_continuation_window_count(options, strategy, folding_steps).unwrap(),
    );
    let expected_window_launches = layers * windows_per_layer;
    let expected_full_rounds = usize::from(windows_per_layer == 0) * layers * (folding_steps - 3);
    let expected_remainder_rounds =
        usize::from(windows_per_layer > 0) * layers * (folding_steps - (3 + 3 * windows_per_layer));
    assert_eq!(output.execution_counts.layers, layers);
    assert_eq!(
        output.execution_counts.window_launches,
        expected_window_launches
    );
    assert_eq!(
        output.execution_counts.legacy_full_rounds,
        expected_full_rounds
    );
    assert_eq!(
        output.execution_counts.legacy_remainder_rounds,
        expected_remainder_rounds
    );
    let proof_sha256 = task8_proof_sha256(&output.proof);
    Task8ExactMemoryRecord {
        schema_version: 1,
        performance_plan_sha256: "27bb732c87371b4ed3c357f8cbe524e1ae3c285150f34cfdc2e601e4163052d8"
            .to_owned(),
        observer_dependency_commit: "2e4a6d5e58a96f94991fbbb5b797c01a830e9ee0".to_owned(),
        observer_closure_audit_sha256:
            "5813895a7bcd4dbb8c5e77575e868ad9925f7be264b63627794e232339be508d".to_owned(),
        inactive_observer_evidence_hook:
            "producer-owned release zero-allocation/unchanged-byte comparison".to_owned(),
        artifact_head: artifact.0.clone(),
        artifact_tree: artifact.1.clone(),
        release_executable: artifact.2.clone(),
        workload_id: workload.to_owned(),
        sample_index,
        pair_index,
        order_in_pair,
        arm: arm.to_owned(),
        backward_options: format!("{options:?}"),
        final_trace_size_log_2: fixture.final_trace_size_log_2,
        configuration,
        backward: output.backward.into(),
        whole: output.whole.into(),
        proof_sha256,
        proof_time_ms_bits: output.proof_time_ms.to_bits(),
        selected_strategy: format!("{strategy:?}"),
        dr_counters_observed: false,
        dr_bundle_final_log: None,
        dr_prepared_layer_count: None,
        dr_r0_launch_count: None,
        dr_continuation_launch_count: None,
        dr_tail_launch_count: None,
        main_continuation_window_launch_count: output.execution_counts.window_launches,
        main_legacy_full_round_count: output.execution_counts.legacy_full_rounds,
        main_legacy_remainder_round_count: output.execution_counts.legacy_remainder_rounds,
    }
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
#[test]
#[ignore]
fn main_continuation_exact_memory_review() {
    let artifact = task8_artifact_identity();
    let baseline_options = GkrBackwardOptions {
        windowed_r0: true,
        windowed_main_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let new_options = GkrBackwardOptions {
        windowed_r0: true,
        windowed_main_continuations: true,
        ..GkrBackwardOptions::default()
    };
    let mut selected_rows = 0usize;
    for (workload, build) in task8_fixture_builders() {
        let fixture = build();
        let configured = take_task8_configured_context();
        let configuration = Task8AllocatorConfiguration::from_fixture(&fixture, configured);
        let fixture_entry = fixture.context.get_device_memory_usage();

        for options in [baseline_options, new_options] {
            let warm = fixture
                .schedule_exact_memory(options)
                .unwrap()
                .finish()
                .unwrap();
            assert_gkr_proof_structure_for_test(&warm.proof, &fixture.prover_config.whir_schedule);
            let warm_whole = Task8MemoryIntervalRecord::from(warm.whole);
            let warm_backward = Task8MemoryIntervalRecord::from(warm.backward);
            assert_eq!(
                (
                    warm_whole.start_physical_backing_bytes,
                    warm_whole.start_logical_live_bytes,
                ),
                (
                    fixture_entry.physical_backing_bytes,
                    fixture_entry.logical_live_bytes,
                ),
                "Task 8 {workload} warmup whole-proof entry drifted"
            );
            validate_exact_memory_return_chain("warmup", warm_backward, warm_whole).unwrap();
        }

        let mut deterministic_peaks = std::collections::BTreeMap::new();
        let mut per_arm_maxima = std::collections::BTreeMap::new();
        let stable_whole_entry = (
            fixture_entry.physical_backing_bytes,
            fixture_entry.logical_live_bytes,
        );
        let order = [
            ("baseline", baseline_options),
            ("new", new_options),
            ("new", new_options),
            ("baseline", baseline_options),
        ];
        let mut sample_index = 0usize;
        for block in 0..3 {
            let mut rows = Vec::new();
            for (order_index, (arm, options)) in order.into_iter().enumerate() {
                let output = fixture
                    .schedule_exact_memory(options)
                    .unwrap()
                    .finish()
                    .unwrap();
                let pair_index = 2 * block + usize::from(order_index >= 2);
                let order_in_pair = order_index % 2;
                let record = task8_memory_record(
                    workload,
                    sample_index,
                    pair_index,
                    order_in_pair,
                    arm,
                    options,
                    configuration,
                    &artifact,
                    &fixture,
                    output,
                );
                let peaks = (
                    record.backward.peak_physical_backing_bytes,
                    record.backward.peak_logical_live_bytes,
                    record.whole.peak_physical_backing_bytes,
                    record.whole.peak_logical_live_bytes,
                );
                let whole_entry = (
                    record.whole.start_physical_backing_bytes,
                    record.whole.start_logical_live_bytes,
                );
                assert_eq!(
                    whole_entry, stable_whole_entry,
                    "Task 8 {workload} whole-proof entry drifted across warmups/measured rows"
                );
                if let Some(previous) = deterministic_peaks.insert(arm, peaks) {
                    assert_eq!(
                        previous, peaks,
                        "Task 8 {workload} {arm} peaks are nondeterministic"
                    );
                }
                per_arm_maxima
                    .entry(arm)
                    .and_modify(|maxima: &mut (usize, usize, usize, usize)| {
                        maxima.0 = maxima.0.max(peaks.0);
                        maxima.1 = maxima.1.max(peaks.1);
                        maxima.2 = maxima.2.max(peaks.2);
                        maxima.3 = maxima.3.max(peaks.3);
                    })
                    .or_insert(peaks);
                eprintln!(
                    "TASK8_EXACT_MEMORY {}",
                    serde_json::to_string(&record).unwrap()
                );
                rows.push(record);
                sample_index += 1;
                selected_rows += 1;
            }
            compare_task8_exact_memory(&rows[0], &rows[1])
                .unwrap_or_else(|error| panic!("{error}"));
            compare_task8_exact_memory(&rows[3], &rows[2])
                .unwrap_or_else(|error| panic!("{error}"));
        }
        assert_eq!(per_arm_maxima.len(), 2);
        let baseline_maxima = per_arm_maxima["baseline"];
        let new_maxima = per_arm_maxima["new"];
        for (metric, baseline_bytes, new_bytes) in [
            ("backward physical", baseline_maxima.0, new_maxima.0),
            ("backward logical", baseline_maxima.1, new_maxima.1),
            ("whole physical", baseline_maxima.2, new_maxima.2),
            ("whole logical", baseline_maxima.3, new_maxima.3),
        ] {
            assert!(
                new_bytes <= baseline_bytes,
                "Task 8 {workload} per-arm maximum {metric} increased: baseline={baseline_bytes} new={new_bytes}"
            );
        }
        eprintln!(
            "TASK8_EXACT_MEMORY_MAXIMA workload={workload} baseline={:?} new={:?}",
            per_arm_maxima["baseline"], per_arm_maxima["new"]
        );
    }
    assert_eq!(selected_rows, 12 * 12);
}
