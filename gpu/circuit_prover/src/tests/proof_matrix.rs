use super::*;
use gpu_gkr::BackwardExecutionStrategy;
use serde::Serialize;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

const TASK6_EXACT_MEMORY_SCHEMA_VERSION: u32 = 2;
const TASK6_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;
const TASK6_DEVICE_ARENA_BYTES: u64 = 64u64 << 30;
const TASK6_MAX_DEVICE_BLOCKS: u64 = TASK6_DEVICE_ARENA_BYTES >> TASK6_ALLOCATOR_BLOCK_LOG_SIZE;
const TASK6_SMALL_ALLOCATOR_LOG_CHUNK_SIZE: u32 = 8;
const TASK6_SMALL_ALLOCATOR_POOL_BLOCKS: u64 = 16;
const TASK6_WORKLOAD_SOURCE: &str = "prepare_unified_proof_fixture";
const TASK6_FIXTURE_LAYOUT_PATH: &str =
    "cs/compiled_circuits/unified_reduced_machine_layout_gkr.json";
const TASK6_FIXTURE_LAYOUT_SHA256: &str =
    "53331555ffd08dab4dd3f71be8011528a52d3584f435320a8a0b2ffd9121add8";
const TASK6_FIXTURE_BINARY_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.bin";
const TASK6_FIXTURE_TEXT_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.text";
const TASK6_FIXTURE_NON_DETERMINISM_WORDS: [u32; 2] = [50, 0xDEAD_BEEF];

#[derive(Clone, Debug, Serialize)]
struct Task6ExactMemoryRecord {
    schema_version: u32,
    artifact_head: String,
    artifact_tree: String,
    release_executable: String,
    release_executable_sha256: String,
    workload_id: String,
    sample_index: u64,
    pair_index: u64,
    order_in_pair: u64,
    arm: String,
    backward_options: String,
    final_trace_size_log_2: u32,
    allocator_block_log_size: u32,
    max_device_allocation_blocks_count: u64,
    actual_device_allocation_blocks_count: u64,
    actual_device_arena_bytes: u64,
    small_allocator_enabled: bool,
    small_allocator_log_chunk_size: u32,
    small_allocator_pool_blocks: u64,
    backward_start_physical_backing_bytes: u64,
    backward_start_logical_live_bytes: u64,
    backward_peak_physical_backing_bytes: u64,
    backward_peak_logical_live_bytes: u64,
    backward_summed_requested_bytes: u64,
    backward_peak_window_end_physical_backing_bytes: u64,
    backward_peak_window_end_logical_live_bytes: u64,
    backward_return_physical_backing_bytes: u64,
    backward_return_logical_live_bytes: u64,
    whole_start_physical_backing_bytes: u64,
    whole_start_logical_live_bytes: u64,
    whole_peak_physical_backing_bytes: u64,
    whole_peak_logical_live_bytes: u64,
    whole_summed_requested_bytes: u64,
    whole_peak_window_end_physical_backing_bytes: u64,
    whole_peak_window_end_logical_live_bytes: u64,
    whole_return_physical_backing_bytes: u64,
    whole_return_logical_live_bytes: u64,
    proof_sha256: String,
    host_end_to_end_time_ns: u64,
    proof_time_ms: u64,
    cuda_proof_time_ms: f32,
    selected_strategy: String,
    dr_bundle_final_log: Option<u32>,
    dr_prepared_layer_count: u64,
    legacy_dr_execution_count: u64,
    dr_r0_launch_count: u64,
    dr_continuation_launch_count: u64,
    dr_tail_launch_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task6ExactMemoryMismatch {
    field: &'static str,
    baseline: u64,
    new: u64,
    delta: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task6FixtureTraceLenMismatch {
    layout_declared_trace_len: usize,
    prepared_fixture_trace_len: usize,
}

impl std::fmt::Display for Task6FixtureTraceLenMismatch {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "fixture trace_len mismatch: layout_declared_trace_len={} prepared_fixture_trace_len={}",
            self.layout_declared_trace_len, self.prepared_fixture_trace_len
        )
    }
}

fn task6_fixture_trace_len_from_layout_value(layout: &serde_json::Value) -> Result<usize, String> {
    let trace_len = layout
        .get("trace_len")
        .ok_or_else(|| "fixture layout must contain top-level trace_len".to_owned())?
        .as_u64()
        .ok_or_else(|| "fixture layout trace_len must be an unsigned integer".to_owned())?;
    if trace_len == 0 {
        return Err("fixture layout trace_len must be nonzero".to_owned());
    }
    trace_len
        .try_into()
        .map_err(|_| format!("fixture layout trace_len does not fit usize: {trace_len}"))
}

fn task6_fixture_trace_len_from_layout(path: &std::path::Path) -> Result<usize, String> {
    let file = std::fs::File::open(path)
        .map_err(|error| format!("failed to open fixture layout {}: {error}", path.display()))?;
    let layout: serde_json::Value = serde_json::from_reader(file)
        .map_err(|error| format!("failed to parse fixture layout {}: {error}", path.display()))?;
    task6_fixture_trace_len_from_layout_value(&layout)
}

fn require_task6_prepared_trace_len_matches_layout(
    layout_declared_trace_len: usize,
    prepared_fixture_trace_len: usize,
) -> Result<(), Task6FixtureTraceLenMismatch> {
    if prepared_fixture_trace_len == layout_declared_trace_len {
        Ok(())
    } else {
        Err(Task6FixtureTraceLenMismatch {
            layout_declared_trace_len,
            prepared_fixture_trace_len,
        })
    }
}

impl std::fmt::Display for Task6ExactMemoryMismatch {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} mismatch: baseline={} bytes new={} bytes delta={:+} bytes",
            self.field, self.baseline, self.new, self.delta
        )
    }
}

fn exact_memory_mismatch(field: &'static str, baseline: u64, new: u64) -> Task6ExactMemoryMismatch {
    Task6ExactMemoryMismatch {
        field,
        baseline,
        new,
        delta: i128::from(new) - i128::from(baseline),
    }
}

fn require_exact_memory_equal(
    field: &'static str,
    baseline: u64,
    new: u64,
) -> Result<(), Task6ExactMemoryMismatch> {
    if baseline == new {
        Ok(())
    } else {
        Err(exact_memory_mismatch(field, baseline, new))
    }
}

fn require_exact_memory_nonincrease(
    field: &'static str,
    baseline: u64,
    new: u64,
) -> Result<(), Task6ExactMemoryMismatch> {
    if new <= baseline {
        Ok(())
    } else {
        Err(exact_memory_mismatch(field, baseline, new))
    }
}

fn compare_task6_exact_memory_pair(
    baseline: &Task6ExactMemoryRecord,
    new: &Task6ExactMemoryRecord,
) -> Result<(), Task6ExactMemoryMismatch> {
    require_exact_memory_equal(
        "allocator_block_log_size",
        u64::from(baseline.allocator_block_log_size),
        u64::from(new.allocator_block_log_size),
    )?;
    require_exact_memory_equal(
        "max_device_allocation_blocks_count",
        baseline.max_device_allocation_blocks_count,
        new.max_device_allocation_blocks_count,
    )?;
    require_exact_memory_equal(
        "actual_device_allocation_blocks_count",
        baseline.actual_device_allocation_blocks_count,
        new.actual_device_allocation_blocks_count,
    )?;
    require_exact_memory_equal(
        "actual_device_arena_bytes",
        baseline.actual_device_arena_bytes,
        new.actual_device_arena_bytes,
    )?;
    require_exact_memory_equal(
        "small_allocator_enabled",
        u64::from(baseline.small_allocator_enabled),
        u64::from(new.small_allocator_enabled),
    )?;
    require_exact_memory_equal(
        "small_allocator_log_chunk_size",
        u64::from(baseline.small_allocator_log_chunk_size),
        u64::from(new.small_allocator_log_chunk_size),
    )?;
    require_exact_memory_equal(
        "small_allocator_pool_blocks",
        baseline.small_allocator_pool_blocks,
        new.small_allocator_pool_blocks,
    )?;
    require_exact_memory_equal(
        "backward.start.physical_backing_bytes",
        baseline.backward_start_physical_backing_bytes,
        new.backward_start_physical_backing_bytes,
    )?;
    require_exact_memory_equal(
        "backward.start.logical_live_bytes",
        baseline.backward_start_logical_live_bytes,
        new.backward_start_logical_live_bytes,
    )?;
    require_exact_memory_equal(
        "whole.start.physical_backing_bytes",
        baseline.whole_start_physical_backing_bytes,
        new.whole_start_physical_backing_bytes,
    )?;
    require_exact_memory_equal(
        "whole.start.logical_live_bytes",
        baseline.whole_start_logical_live_bytes,
        new.whole_start_logical_live_bytes,
    )?;

    for (field, start, returned) in [
        (
            "baseline.backward.return.physical_backing_bytes",
            baseline.whole_start_physical_backing_bytes,
            baseline.backward_return_physical_backing_bytes,
        ),
        (
            "baseline.backward.return.logical_live_bytes",
            baseline.whole_start_logical_live_bytes,
            baseline.backward_return_logical_live_bytes,
        ),
        (
            "new.backward.return.physical_backing_bytes",
            new.whole_start_physical_backing_bytes,
            new.backward_return_physical_backing_bytes,
        ),
        (
            "new.backward.return.logical_live_bytes",
            new.whole_start_logical_live_bytes,
            new.backward_return_logical_live_bytes,
        ),
        (
            "baseline.whole.return.physical_backing_bytes",
            baseline.whole_start_physical_backing_bytes,
            baseline.whole_return_physical_backing_bytes,
        ),
        (
            "baseline.whole.return.logical_live_bytes",
            baseline.whole_start_logical_live_bytes,
            baseline.whole_return_logical_live_bytes,
        ),
        (
            "new.whole.return.physical_backing_bytes",
            new.whole_start_physical_backing_bytes,
            new.whole_return_physical_backing_bytes,
        ),
        (
            "new.whole.return.logical_live_bytes",
            new.whole_start_logical_live_bytes,
            new.whole_return_logical_live_bytes,
        ),
    ] {
        if field.contains("backward") {
            require_exact_memory_nonincrease(field, start, returned)?;
        } else {
            require_exact_memory_equal(field, start, returned)?;
        }
    }

    for (field, backward_return, whole_return) in [
        (
            "baseline.backward.return_eq_whole.return.physical_backing_bytes",
            baseline.backward_return_physical_backing_bytes,
            baseline.whole_return_physical_backing_bytes,
        ),
        (
            "baseline.backward.return_eq_whole.return.logical_live_bytes",
            baseline.backward_return_logical_live_bytes,
            baseline.whole_return_logical_live_bytes,
        ),
        (
            "new.backward.return_eq_whole.return.physical_backing_bytes",
            new.backward_return_physical_backing_bytes,
            new.whole_return_physical_backing_bytes,
        ),
        (
            "new.backward.return_eq_whole.return.logical_live_bytes",
            new.backward_return_logical_live_bytes,
            new.whole_return_logical_live_bytes,
        ),
    ] {
        require_exact_memory_equal(field, backward_return, whole_return)?;
    }

    require_exact_memory_nonincrease(
        "backward.physical_backing_peak_bytes",
        baseline.backward_peak_physical_backing_bytes,
        new.backward_peak_physical_backing_bytes,
    )?;
    require_exact_memory_nonincrease(
        "backward.logical_live_peak_bytes",
        baseline.backward_peak_logical_live_bytes,
        new.backward_peak_logical_live_bytes,
    )?;
    require_exact_memory_nonincrease(
        "whole.physical_backing_peak_bytes",
        baseline.whole_peak_physical_backing_bytes,
        new.whole_peak_physical_backing_bytes,
    )?;
    require_exact_memory_nonincrease(
        "whole.logical_live_peak_bytes",
        baseline.whole_peak_logical_live_bytes,
        new.whole_peak_logical_live_bytes,
    )?;
    Ok(())
}

const TASK6_RAW_U64_FIELDS: &[&str] = &[
    "actual_device_arena_bytes",
    "backward_start_physical_backing_bytes",
    "backward_start_logical_live_bytes",
    "backward_peak_physical_backing_bytes",
    "backward_peak_logical_live_bytes",
    "backward_summed_requested_bytes",
    "backward_peak_window_end_physical_backing_bytes",
    "backward_peak_window_end_logical_live_bytes",
    "backward_return_physical_backing_bytes",
    "backward_return_logical_live_bytes",
    "whole_start_physical_backing_bytes",
    "whole_start_logical_live_bytes",
    "whole_peak_physical_backing_bytes",
    "whole_peak_logical_live_bytes",
    "whole_summed_requested_bytes",
    "whole_peak_window_end_physical_backing_bytes",
    "whole_peak_window_end_logical_live_bytes",
    "whole_return_physical_backing_bytes",
    "whole_return_logical_live_bytes",
    "host_end_to_end_time_ns",
];

fn validate_task6_exact_memory_schema(value: &serde_json::Value) -> Result<(), String> {
    let object = value
        .as_object()
        .ok_or_else(|| "raw record must be a JSON object".to_owned())?;
    for field in TASK6_RAW_U64_FIELDS {
        let value = object
            .get(*field)
            .ok_or_else(|| format!("missing raw integer field {field}"))?;
        if value.as_u64().is_none() {
            return Err(format!("raw field {field} must be an integer byte value"));
        }
    }
    if object
        .keys()
        .any(|field| field.to_ascii_lowercase().contains("gib"))
    {
        return Err("raw schema must not contain rounded GiB fields".to_owned());
    }
    Ok(())
}

fn task6_exact_memory_record_for_test(arm: &str) -> Task6ExactMemoryRecord {
    Task6ExactMemoryRecord {
        schema_version: TASK6_EXACT_MEMORY_SCHEMA_VERSION,
        artifact_head: "head".to_owned(),
        artifact_tree: "tree".to_owned(),
        release_executable: "target/release/test".to_owned(),
        release_executable_sha256: "sha256".to_owned(),
        workload_id: "canonical-unified-fixture-for-comparator".to_owned(),
        sample_index: 0,
        pair_index: 0,
        order_in_pair: 0,
        arm: arm.to_owned(),
        backward_options: format!("windowed_dr={}", arm == "new"),
        final_trace_size_log_2: 4,
        allocator_block_log_size: TASK6_ALLOCATOR_BLOCK_LOG_SIZE,
        max_device_allocation_blocks_count: TASK6_MAX_DEVICE_BLOCKS,
        actual_device_allocation_blocks_count: TASK6_MAX_DEVICE_BLOCKS,
        actual_device_arena_bytes: TASK6_DEVICE_ARENA_BYTES,
        small_allocator_enabled: true,
        small_allocator_log_chunk_size: TASK6_SMALL_ALLOCATOR_LOG_CHUNK_SIZE,
        small_allocator_pool_blocks: TASK6_SMALL_ALLOCATOR_POOL_BLOCKS,
        backward_start_physical_backing_bytes: 100,
        backward_start_logical_live_bytes: 10,
        backward_peak_physical_backing_bytes: 200,
        backward_peak_logical_live_bytes: 120,
        backward_summed_requested_bytes: 90,
        backward_peak_window_end_physical_backing_bytes: 150,
        backward_peak_window_end_logical_live_bytes: 80,
        backward_return_physical_backing_bytes: 100,
        backward_return_logical_live_bytes: 10,
        whole_start_physical_backing_bytes: 100,
        whole_start_logical_live_bytes: 10,
        whole_peak_physical_backing_bytes: 300,
        whole_peak_logical_live_bytes: 220,
        whole_summed_requested_bytes: 190,
        whole_peak_window_end_physical_backing_bytes: 175,
        whole_peak_window_end_logical_live_bytes: 90,
        whole_return_physical_backing_bytes: 100,
        whole_return_logical_live_bytes: 10,
        proof_sha256: "proof".to_owned(),
        host_end_to_end_time_ns: 1_000_000,
        proof_time_ms: 1,
        cuda_proof_time_ms: 1.0,
        selected_strategy: "WindowedR0".to_owned(),
        dr_bundle_final_log: (arm == "new").then_some(4),
        dr_prepared_layer_count: u64::from(arm == "new"),
        legacy_dr_execution_count: 1,
        dr_r0_launch_count: 0,
        dr_continuation_launch_count: 0,
        dr_tail_launch_count: 0,
    }
}

#[test]
fn cpu_task6_exact_memory_comparator_rejects_each_positive_byte_delta() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    for (field, mutate) in [
        ("backward.physical_backing_peak_bytes", 0usize),
        ("backward.logical_live_peak_bytes", 1),
        ("whole.physical_backing_peak_bytes", 2),
        ("whole.logical_live_peak_bytes", 3),
    ] {
        let mut new = task6_exact_memory_record_for_test("new");
        match mutate {
            0 => new.backward_peak_physical_backing_bytes += 1,
            1 => new.backward_peak_logical_live_bytes += 1,
            2 => new.whole_peak_physical_backing_bytes += 1,
            3 => new.whole_peak_logical_live_bytes += 1,
            _ => unreachable!(),
        }
        let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
        assert_eq!(error.field, field);
        assert_eq!(error.delta, 1);
    }
}

#[test]
fn cpu_task6_exact_memory_comparator_rejects_hidden_small_pool_growth() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    let mut new = task6_exact_memory_record_for_test("new");
    new.backward_peak_logical_live_bytes += 1;
    let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
    assert_eq!(error.field, "backward.logical_live_peak_bytes");
}

#[test]
fn cpu_task6_exact_memory_comparator_rejects_whole_peak_masking() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    let mut new = task6_exact_memory_record_for_test("new");
    new.backward_peak_physical_backing_bytes += 1;
    let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
    assert_eq!(error.field, "backward.physical_backing_peak_bytes");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Task6ClaimBufferPhase {
    old_claims_retired_before_new_claims: bool,
    overlap_bytes: u64,
}

fn task6_claim_buffer_phase_order(retire_old_before_allocate_new: bool) -> Task6ClaimBufferPhase {
    const CLAIM_BYTES: u64 = 112 * std::mem::size_of::<E4>() as u64;
    Task6ClaimBufferPhase {
        old_claims_retired_before_new_claims: retire_old_before_allocate_new,
        overlap_bytes: if retire_old_before_allocate_new {
            0
        } else {
            CLAIM_BYTES
        },
    }
}

#[test]
fn cpu_exact_memory_claim_buffers_retire_before_replacement_allocation() {
    let corrected = task6_claim_buffer_phase_order(true);
    assert!(corrected.old_claims_retired_before_new_claims);
    assert_eq!(corrected.overlap_bytes, 0);

    // Mutation control: reversing the lifetime order recreates the measured
    // 3,584-byte logical-live overlap and must fail the modeled gate.
    let mutated = task6_claim_buffer_phase_order(false);
    assert!(!mutated.old_claims_retired_before_new_claims);
    assert_eq!(mutated.overlap_bytes, 3_584);
    assert!(mutated.overlap_bytes > corrected.overlap_bytes);
}

#[test]
fn cpu_task6_exact_memory_record_is_raw_integer_bytes() {
    let record = task6_exact_memory_record_for_test("baseline");
    let mut value = serde_json::to_value(record).unwrap();
    validate_task6_exact_memory_schema(&value).unwrap();
    value
        .as_object_mut()
        .unwrap()
        .remove("whole_peak_logical_live_bytes");
    let error = validate_task6_exact_memory_schema(&value).unwrap_err();
    assert!(error.contains("whole_peak_logical_live_bytes"));
}

#[test]
fn cpu_task6_exact_memory_record_rejects_entry_config_and_return_drift() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    for (field, mutate) in [
        ("backward.start.physical_backing_bytes", 0usize),
        ("whole.start.logical_live_bytes", 1),
        ("allocator_block_log_size", 2),
        ("max_device_allocation_blocks_count", 3),
        ("actual_device_allocation_blocks_count", 4),
        ("actual_device_arena_bytes", 5),
        ("small_allocator_enabled", 6),
        ("small_allocator_log_chunk_size", 7),
        ("small_allocator_pool_blocks", 8),
        ("new.backward.return.physical_backing_bytes", 9),
        ("new.whole.return.logical_live_bytes", 10),
    ] {
        let mut new = task6_exact_memory_record_for_test("new");
        match mutate {
            0 => new.backward_start_physical_backing_bytes += 1,
            1 => new.whole_start_logical_live_bytes += 1,
            2 => new.allocator_block_log_size += 1,
            3 => new.max_device_allocation_blocks_count += 1,
            4 => new.actual_device_allocation_blocks_count += 1,
            5 => new.actual_device_arena_bytes += 1,
            6 => new.small_allocator_enabled = false,
            7 => new.small_allocator_log_chunk_size += 1,
            8 => new.small_allocator_pool_blocks += 1,
            9 => new.backward_return_physical_backing_bytes += 1,
            10 => new.whole_return_logical_live_bytes += 1,
            _ => unreachable!(),
        }
        let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
        assert_eq!(error.field, field);
    }

    let mut baseline = task6_exact_memory_record_for_test("baseline");
    let mut new = task6_exact_memory_record_for_test("new");
    baseline.whole_start_logical_live_bytes += 1;
    new.whole_start_logical_live_bytes += 1;
    let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
    assert_eq!(error.field, "baseline.backward.return.logical_live_bytes");
}

#[test]
fn cpu_exact_memory_fixture_trace_len_provenance_rejects_prepared_mismatch() {
    let layout_path = test_artifact_path(TASK6_FIXTURE_LAYOUT_PATH);
    assert_eq!(task6_sha256_file(&layout_path), TASK6_FIXTURE_LAYOUT_SHA256);
    let layout_declared_trace_len = task6_fixture_trace_len_from_layout(&layout_path).unwrap();
    assert_eq!(layout_declared_trace_len, 1usize << 23);
    require_task6_prepared_trace_len_matches_layout(
        layout_declared_trace_len,
        layout_declared_trace_len,
    )
    .unwrap();

    let prepared_fixture_trace_len = layout_declared_trace_len.checked_add(1).unwrap();
    let error = require_task6_prepared_trace_len_matches_layout(
        layout_declared_trace_len,
        prepared_fixture_trace_len,
    )
    .unwrap_err();
    assert_eq!(error.layout_declared_trace_len, layout_declared_trace_len);
    assert_eq!(error.prepared_fixture_trace_len, prepared_fixture_trace_len);
    assert!(error
        .to_string()
        .contains("layout_declared_trace_len=8388608"));
    assert!(error
        .to_string()
        .contains("prepared_fixture_trace_len=8388609"));

    for invalid_layout in [
        serde_json::json!({}),
        serde_json::json!({"trace_len": "8388608"}),
        serde_json::json!({"trace_len": 0}),
    ] {
        assert!(task6_fixture_trace_len_from_layout_value(&invalid_layout).is_err());
    }
}

#[test]
fn cpu_exact_memory_host_interval_starts_before_preflight_and_transfers() {
    const SOURCE: &str = include_str!("proof_matrix.rs");
    // Anchor on the name only: the seam carries generic parameters, and the
    // oracle must survive a signature change while still failing on a moved
    // boundary.
    let schedule_start = SOURCE
        .find("\n    fn schedule_task6_exact_memory_prove")
        .map(|offset| offset + 1)
        .expect("exact-memory scheduling seam must remain present");
    let schedule_end = SOURCE[schedule_start..]
        .find("fn task6_checked_u64(")
        .map(|offset| schedule_start + offset)
        .expect("exact-memory scheduling seam must have a stable end anchor");
    let schedule = &SOURCE[schedule_start..schedule_end];
    let check_order = |candidate: &str| {
        let timer_start = candidate
            .find("let host_start = Instant::now();")
            .ok_or("raw host timer must remain explicit")?;
        let preflight = candidate
            .find("construct_after_windowed_backward_preflight(")
            .ok_or("shared preflight must remain in the measured seam")?;
        let transfer_schedule = candidate
            .find("transfers.schedule(&self.context)?;")
            .ok_or("H2D scheduling must remain in the measured seam")?;
        let backward_observer = candidate
            .find("ProofMemoryHighWaterSink::new")
            .ok_or("backward observer boundary must remain explicit")?;
        if timer_start >= preflight {
            return Err("host timer starts after arm-dependent preflight");
        }
        if timer_start >= transfer_schedule {
            return Err("host timer starts after H2D transfer scheduling");
        }
        if transfer_schedule >= backward_observer {
            return Err("backward observer starts before preflight/transfers finish");
        }
        Ok(())
    };
    check_order(schedule).unwrap();
    assert!(
        SOURCE.contains("host_end_to_end_time_ns"),
        "the accepted interval must retain an unrounded integer-nanosecond record"
    );

    let moved_late = schedule
        .replacen("        let host_start = Instant::now();\n", "", 1)
        .replacen(
            "        let mem_before_prove =",
            "        let host_start = Instant::now();\n        let mem_before_prove =",
            1,
        );
    assert_eq!(
        check_order(&moved_late),
        Err("host timer starts after arm-dependent preflight"),
        "moving the timer to its former late boundary must fail the oracle"
    );
}

struct Task6MeasuredProofJob<'context> {
    job: GpuGKRProofJob<'static, 'context, Global>,
    backward: crate::proof::ProofMemoryHighWaterSink<'context>,
    whole: gpu_prover_context::DeviceMemoryHighWaterObserver<'context>,
    sequence: Arc<AtomicUsize>,
    whole_start_sequence: usize,
    host_start_sequence: usize,
    transfer_schedule_sequence: usize,
    host_start: Instant,
}

struct Task6MeasuredProof {
    proof: GKRProof<BF, E4, DefaultTreeConstructor>,
    host_end_to_end_time_ns: u64,
    proof_time_ms: u64,
    cuda_proof_time_ms: f32,
    backward: gpu_prover_context::PoolMemoryHighWaterReport,
    whole: gpu_prover_context::PoolMemoryHighWaterReport,
    legacy_dr_execution_count: usize,
    dr_prepared_layer_count: usize,
    dr_bundle_final_log: Option<u32>,
}

impl Task6MeasuredProofJob<'_> {
    fn finish(self) -> GpuProveResult<Task6MeasuredProof> {
        let (proof, cuda_proof_time_ms) = self.job.finish()?;
        let job_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);
        let backward = self.backward.finish();
        let backward_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);
        let whole = self.whole.finish();
        let whole_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);

        assert!(self.whole_start_sequence < self.host_start_sequence);
        assert!(self.host_start_sequence < self.transfer_schedule_sequence);
        assert!(self.transfer_schedule_sequence < backward.start_sequence);
        assert!(backward.start_sequence < backward.seal_sequence);
        assert!(backward.seal_sequence < job_finish_sequence);
        assert!(job_finish_sequence < backward_finish_sequence);
        assert!(backward_finish_sequence <= whole_finish_sequence);

        let host_elapsed = self.host_start.elapsed();
        Ok(Task6MeasuredProof {
            proof,
            host_end_to_end_time_ns: host_elapsed.as_nanos().try_into().unwrap(),
            proof_time_ms: host_elapsed.as_millis().try_into().unwrap(),
            cuda_proof_time_ms,
            backward: backward.backward,
            whole,
            legacy_dr_execution_count: backward.legacy_dr_execution_count,
            dr_prepared_layer_count: backward.dr_prepared_layer_count,
            dr_bundle_final_log: backward.dr_bundle_final_log,
        })
    }
}

impl BasicUnrolledFixture {
    fn schedule_task6_exact_memory_prove<'context>(
        &'context self,
        backward_options: GkrBackwardOptions,
    ) -> GpuProveResult<Task6MeasuredProofJob<'_>> {
        let sequence = Arc::new(AtomicUsize::new(0));
        let whole = self.context.observe_device_memory_high_water();
        let whole_start_sequence = sequence.fetch_add(1, Ordering::SeqCst);
        let host_start_sequence = sequence.fetch_add(1, Ordering::SeqCst);
        let host_start = Instant::now();
        let strategy = resolve_backward_execution_strategy(
            &self.gkr_programs,
            &self.prover_config,
            backward_options,
        );
        let mut transfers = construct_after_windowed_backward_preflight(
            &self.gkr_programs,
            strategy,
            backward_options,
            self.final_trace_size_log_2,
            || self.create_transfers(),
        )
        .unwrap()?;

        let h2d_stream = self.context.get_h2d_stream();
        let transfer_range = Range::new("gkr.proof.h2d_transfers")?;
        transfer_range.start(h2d_stream)?;
        transfers.schedule(&self.context)?;
        transfer_range.end(h2d_stream)?;
        let transfer_schedule_sequence = sequence.fetch_add(1, Ordering::SeqCst);

        let mem_before_prove = self.context.get_device_memory_usage();
        let mut backward = crate::proof::ProofMemoryHighWaterSink::new(Arc::clone(&sequence));
        let mut job = crate::proof::prove_measured::<Global>(
            &self.gkr_programs,
            &self.prover_config,
            self.final_trace_size_log_2,
            transfers,
            backward_options,
            &mut backward,
            &self.context,
        )?;
        let mem_after_prove = self.context.get_device_memory_usage();
        assert_eq!(
            mem_after_prove, mem_before_prove,
            "measured prove must release every proof-owned device allocation"
        );
        job.ranges.insert(0, transfer_range);
        Ok(Task6MeasuredProofJob {
            job,
            backward,
            whole,
            sequence,
            whole_start_sequence,
            host_start_sequence,
            transfer_schedule_sequence,
            host_start,
        })
    }
}

fn task6_checked_u64(value: usize, field: &str) -> u64 {
    value
        .try_into()
        .unwrap_or_else(|_| panic!("{field} does not fit in u64: {value}"))
}

fn task6_command_stdout(program: &str, args: &[&str]) -> String {
    let output = Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run {program}: {error}"));
    assert!(
        output.status.success(),
        "{program} {:?} failed: {}",
        args,
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

fn task6_sha256_bytes(bytes: &[u8]) -> String {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("sha256sum must be available for the exact-memory gate");
    child.stdin.as_mut().unwrap().write_all(bytes).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn task6_sha256_file(path: &std::path::Path) -> String {
    task6_command_stdout("sha256sum", &[path.to_str().unwrap()])
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn task6_proof_sha256(proof: &GKRProof<BF, E4, DefaultTreeConstructor>) -> String {
    task6_sha256_bytes(&serde_json::to_vec_pretty(proof).unwrap())
}

fn task6_record_from_finished(
    finished: &Task6MeasuredProof,
    artifact_head: &str,
    artifact_tree: &str,
    release_executable: &str,
    release_executable_sha256: &str,
    workload_id: &str,
    sample_index: usize,
    options: GkrBackwardOptions,
    selected_strategy: BackwardExecutionStrategy,
    final_trace_size_log_2: u32,
    actual_device_arena_bytes: usize,
) -> Task6ExactMemoryRecord {
    let pair_index = sample_index / 2;
    let order_in_pair = sample_index % 2;
    let arm = if options.windowed_dr {
        "new"
    } else {
        "baseline"
    };
    let backward = finished.backward;
    let whole = finished.whole;
    Task6ExactMemoryRecord {
        schema_version: TASK6_EXACT_MEMORY_SCHEMA_VERSION,
        artifact_head: artifact_head.to_owned(),
        artifact_tree: artifact_tree.to_owned(),
        release_executable: release_executable.to_owned(),
        release_executable_sha256: release_executable_sha256.to_owned(),
        workload_id: workload_id.to_owned(),
        sample_index: sample_index.try_into().unwrap(),
        pair_index: pair_index.try_into().unwrap(),
        order_in_pair: order_in_pair.try_into().unwrap(),
        arm: arm.to_owned(),
        backward_options: format!("{options:?}"),
        final_trace_size_log_2,
        allocator_block_log_size: TASK6_ALLOCATOR_BLOCK_LOG_SIZE,
        max_device_allocation_blocks_count: TASK6_MAX_DEVICE_BLOCKS,
        actual_device_allocation_blocks_count: task6_checked_u64(
            actual_device_arena_bytes >> TASK6_ALLOCATOR_BLOCK_LOG_SIZE,
            "actual_device_allocation_blocks_count",
        ),
        actual_device_arena_bytes: task6_checked_u64(
            actual_device_arena_bytes,
            "actual_device_arena_bytes",
        ),
        small_allocator_enabled: true,
        small_allocator_log_chunk_size: TASK6_SMALL_ALLOCATOR_LOG_CHUNK_SIZE,
        small_allocator_pool_blocks: TASK6_SMALL_ALLOCATOR_POOL_BLOCKS,
        backward_start_physical_backing_bytes: task6_checked_u64(
            backward.start.physical_backing_bytes,
            "backward_start_physical_backing_bytes",
        ),
        backward_start_logical_live_bytes: task6_checked_u64(
            backward.start.logical_live_bytes,
            "backward_start_logical_live_bytes",
        ),
        backward_peak_physical_backing_bytes: task6_checked_u64(
            backward.physical_backing_peak_bytes,
            "backward_peak_physical_backing_bytes",
        ),
        backward_peak_logical_live_bytes: task6_checked_u64(
            backward.logical_live_peak_bytes,
            "backward_peak_logical_live_bytes",
        ),
        backward_summed_requested_bytes: task6_checked_u64(
            backward.summed_requested_bytes,
            "backward_summed_requested_bytes",
        ),
        backward_peak_window_end_physical_backing_bytes: task6_checked_u64(
            backward.peak_window_end.physical_backing_bytes,
            "backward_peak_window_end_physical_backing_bytes",
        ),
        backward_peak_window_end_logical_live_bytes: task6_checked_u64(
            backward.peak_window_end.logical_live_bytes,
            "backward_peak_window_end_logical_live_bytes",
        ),
        backward_return_physical_backing_bytes: task6_checked_u64(
            backward.return_to_entry.physical_backing_bytes,
            "backward_return_physical_backing_bytes",
        ),
        backward_return_logical_live_bytes: task6_checked_u64(
            backward.return_to_entry.logical_live_bytes,
            "backward_return_logical_live_bytes",
        ),
        whole_start_physical_backing_bytes: task6_checked_u64(
            whole.start.physical_backing_bytes,
            "whole_start_physical_backing_bytes",
        ),
        whole_start_logical_live_bytes: task6_checked_u64(
            whole.start.logical_live_bytes,
            "whole_start_logical_live_bytes",
        ),
        whole_peak_physical_backing_bytes: task6_checked_u64(
            whole.physical_backing_peak_bytes,
            "whole_peak_physical_backing_bytes",
        ),
        whole_peak_logical_live_bytes: task6_checked_u64(
            whole.logical_live_peak_bytes,
            "whole_peak_logical_live_bytes",
        ),
        whole_summed_requested_bytes: task6_checked_u64(
            whole.summed_requested_bytes,
            "whole_summed_requested_bytes",
        ),
        whole_peak_window_end_physical_backing_bytes: task6_checked_u64(
            whole.peak_window_end.physical_backing_bytes,
            "whole_peak_window_end_physical_backing_bytes",
        ),
        whole_peak_window_end_logical_live_bytes: task6_checked_u64(
            whole.peak_window_end.logical_live_bytes,
            "whole_peak_window_end_logical_live_bytes",
        ),
        whole_return_physical_backing_bytes: task6_checked_u64(
            whole.return_to_entry.physical_backing_bytes,
            "whole_return_physical_backing_bytes",
        ),
        whole_return_logical_live_bytes: task6_checked_u64(
            whole.return_to_entry.logical_live_bytes,
            "whole_return_logical_live_bytes",
        ),
        proof_sha256: task6_proof_sha256(&finished.proof),
        host_end_to_end_time_ns: finished.host_end_to_end_time_ns,
        proof_time_ms: finished.proof_time_ms,
        cuda_proof_time_ms: finished.cuda_proof_time_ms,
        selected_strategy: format!("{selected_strategy:?}"),
        dr_bundle_final_log: finished.dr_bundle_final_log,
        dr_prepared_layer_count: finished.dr_prepared_layer_count.try_into().unwrap(),
        legacy_dr_execution_count: finished.legacy_dr_execution_count.try_into().unwrap(),
        dr_r0_launch_count: 0,
        dr_continuation_launch_count: 0,
        dr_tail_launch_count: 0,
    }
}

fn task6_assert_peak_determinism(rows: &[Task6ExactMemoryRecord], arm: &str) {
    let mut matching = rows.iter().filter(|row| row.arm == arm);
    let first = matching.next().expect("each arm must have measured rows");
    let expected = (
        first.backward_peak_physical_backing_bytes,
        first.backward_peak_logical_live_bytes,
        first.whole_peak_physical_backing_bytes,
        first.whole_peak_logical_live_bytes,
    );
    for row in matching {
        assert_eq!(
            (
                row.backward_peak_physical_backing_bytes,
                row.backward_peak_logical_live_bytes,
                row.whole_peak_physical_backing_bytes,
                row.whole_peak_logical_live_bytes,
            ),
            expected,
            "all {arm} repetitions must have deterministic four-cell peaks"
        );
    }
}

fn task6_assert_maxima_nonincrease(rows: &[Task6ExactMemoryRecord]) {
    let maxima = |arm: &str, field: fn(&Task6ExactMemoryRecord) -> u64| {
        rows.iter()
            .filter(|row| row.arm == arm)
            .map(field)
            .max()
            .expect("each arm must have measured rows")
    };
    for (field, accessor) in [
        (
            "backward.physical_backing_peak_bytes",
            (|row: &Task6ExactMemoryRecord| row.backward_peak_physical_backing_bytes)
                as fn(&Task6ExactMemoryRecord) -> u64,
        ),
        (
            "backward.logical_live_peak_bytes",
            |row: &Task6ExactMemoryRecord| row.backward_peak_logical_live_bytes,
        ),
        (
            "whole.physical_backing_peak_bytes",
            |row: &Task6ExactMemoryRecord| row.whole_peak_physical_backing_bytes,
        ),
        (
            "whole.logical_live_peak_bytes",
            |row: &Task6ExactMemoryRecord| row.whole_peak_logical_live_bytes,
        ),
    ] {
        require_exact_memory_nonincrease(
            field,
            maxima("baseline", accessor),
            maxima("new", accessor),
        )
        .unwrap_or_else(|error| panic!("{error}"));
    }
}

#[test]
#[ignore]
fn run_dr_task6_exact_memory_review() {
    let output_root = std::env::var("GKR_TASK6_EXACT_MEMORY_OUT")
        .expect("GKR_TASK6_EXACT_MEMORY_OUT must name the immutable evidence directory");
    let output_root = std::path::PathBuf::from(output_root);
    std::fs::create_dir_all(&output_root).unwrap();

    let artifact_head = task6_command_stdout("git", &["rev-parse", "HEAD"]);
    let artifact_tree = task6_command_stdout("git", &["rev-parse", "HEAD^{tree}"]);
    let release_executable = std::env::current_exe().unwrap();
    let release_executable_sha256 = task6_sha256_file(&release_executable);
    let release_executable = release_executable.to_string_lossy().into_owned();
    let fixture_layout_path = test_artifact_path(TASK6_FIXTURE_LAYOUT_PATH);
    let fixture_layout_sha256 = task6_sha256_file(&fixture_layout_path);
    assert_eq!(fixture_layout_sha256, TASK6_FIXTURE_LAYOUT_SHA256);
    let fixture_layout_declared_trace_len =
        task6_fixture_trace_len_from_layout(&fixture_layout_path).unwrap();
    let fixture_binary_sha256 = task6_sha256_file(&test_artifact_path(TASK6_FIXTURE_BINARY_PATH));
    let fixture_text_sha256 = task6_sha256_file(&test_artifact_path(TASK6_FIXTURE_TEXT_PATH));
    let device_census = serde_json::json!({
        "gpu": task6_command_stdout(
            "nvidia-smi",
            &["--query-gpu=name,uuid,driver_version,pstate,clocks.sm,power.draw,memory.free", "--format=csv,noheader,nounits"],
        ),
        "compute_processes": task6_command_stdout(
            "nvidia-smi",
            &["--query-compute-apps=pid,process_name,used_memory", "--format=csv,noheader,nounits"],
        ),
    });

    let fixture = prepare_unified_proof_fixture();
    assert_eq!(
        fixture.base.circuit_type,
        CircuitType::Unrolled(UnrolledCircuitType::Unified)
    );
    let prepared_fixture_trace_len = fixture.base.compiled_circuit.trace_len;
    require_task6_prepared_trace_len_matches_layout(
        fixture_layout_declared_trace_len,
        prepared_fixture_trace_len,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert!(prepared_fixture_trace_len.is_power_of_two());
    assert_eq!(fixture.base.final_trace_size_log_2, 4);
    assert_eq!(
        fixture.base.prover_config.security_level,
        SecurityLevel::Sec80
    );
    let workload_id = format!(
        "canonical-unified-reduced-machine-layout-trace-{prepared_fixture_trace_len}-final-log-{}-sec80-fixed-nd",
        fixture.base.final_trace_size_log_2
    );
    let actual_device_arena_bytes = fixture.base.context.get_mem_size();
    assert_eq!(
        task6_checked_u64(actual_device_arena_bytes, "actual_device_arena_bytes"),
        TASK6_DEVICE_ARENA_BYTES,
        "the fixture must not silently reduce the pinned 64 GiB arena"
    );

    let baseline_options = GkrBackwardOptions {
        windowed_dr: false,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let new_options = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let baseline_strategy = resolve_backward_execution_strategy(
        &fixture.base.gkr_programs,
        &fixture.base.prover_config,
        baseline_options,
    );
    let new_strategy = resolve_backward_execution_strategy(
        &fixture.base.gkr_programs,
        &fixture.base.prover_config,
        new_options,
    );
    assert_eq!(baseline_strategy, new_strategy);
    assert!(!fixture
        .base
        .gkr_programs
        .dr_window_programs_ready(fixture.base.final_trace_size_log_2));

    let mut cold_preflight_count = 0usize;
    preflight_windowed_backward(
        &fixture.base.gkr_programs,
        baseline_strategy,
        baseline_options,
        fixture.base.final_trace_size_log_2,
    )
    .unwrap();
    cold_preflight_count += 1;
    assert!(!fixture
        .base
        .gkr_programs
        .dr_window_programs_ready(fixture.base.final_trace_size_log_2));
    preflight_windowed_backward(
        &fixture.base.gkr_programs,
        new_strategy,
        new_options,
        fixture.base.final_trace_size_log_2,
    )
    .unwrap();
    cold_preflight_count += 1;
    let bundle = fixture
        .base
        .gkr_programs
        .resolve_dr_window_programs(fixture.base.final_trace_size_log_2)
        .unwrap();
    let bundle_again = fixture
        .base
        .gkr_programs
        .resolve_dr_window_programs(fixture.base.final_trace_size_log_2)
        .unwrap();
    assert!(Arc::ptr_eq(&bundle, &bundle_again));
    assert_eq!(
        bundle.final_trace_log(),
        fixture.base.final_trace_size_log_2
    );

    let mut excluded_warmup_count = 0usize;
    for options in [baseline_options, new_options] {
        let (proof, _) = fixture
            .schedule_prove_with(options)
            .unwrap()
            .finish()
            .unwrap();
        assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
        drop(proof);
        excluded_warmup_count += 1;
    }

    let measured_order = [
        baseline_options,
        new_options,
        new_options,
        baseline_options,
        baseline_options,
        new_options,
        new_options,
        baseline_options,
        baseline_options,
        new_options,
        new_options,
        baseline_options,
    ];
    let mut rows = Vec::with_capacity(measured_order.len());
    let mut matched_cpu_reference_proof_count = 0usize;
    for (sample_index, options) in measured_order.into_iter().enumerate() {
        let selected_strategy = resolve_backward_execution_strategy(
            &fixture.base.gkr_programs,
            &fixture.base.prover_config,
            options,
        );
        let finished = fixture
            .base
            .schedule_task6_exact_memory_prove(options)
            .unwrap()
            .finish()
            .unwrap();
        assert_gkr_proof_eq_for_test(&finished.proof, &fixture.expected_cpu_proof);
        matched_cpu_reference_proof_count += 1;
        let row = task6_record_from_finished(
            &finished,
            &artifact_head,
            &artifact_tree,
            &release_executable,
            &release_executable_sha256,
            &workload_id,
            sample_index,
            options,
            selected_strategy,
            fixture.base.final_trace_size_log_2,
            actual_device_arena_bytes,
        );
        validate_task6_exact_memory_schema(&serde_json::to_value(&row).unwrap()).unwrap();
        assert!(row.legacy_dr_execution_count > 0);
        if options.windowed_dr {
            assert!(row.dr_prepared_layer_count > 0);
            assert_eq!(row.dr_prepared_layer_count, row.legacy_dr_execution_count);
            assert_eq!(
                row.dr_bundle_final_log,
                Some(fixture.base.final_trace_size_log_2)
            );
        } else {
            assert_eq!(row.dr_prepared_layer_count, 0);
            assert_eq!(row.dr_bundle_final_log, None);
        }
        assert_eq!(row.dr_r0_launch_count, 0);
        assert_eq!(row.dr_continuation_launch_count, 0);
        assert_eq!(row.dr_tail_launch_count, 0);
        rows.push(row);
    }

    assert_eq!(rows.len(), 12);
    for pair in rows.chunks_exact(2) {
        let (baseline, new) = if pair[0].arm == "baseline" {
            (&pair[0], &pair[1])
        } else {
            (&pair[1], &pair[0])
        };
        assert_eq!(baseline.arm, "baseline");
        assert_eq!(new.arm, "new");
        assert_eq!(baseline.proof_sha256, new.proof_sha256);
        assert_eq!(baseline.selected_strategy, new.selected_strategy);
        compare_task6_exact_memory_pair(baseline, new).unwrap_or_else(|error| panic!("{error}"));
    }
    let expected_proof_sha256 = &rows[0].proof_sha256;
    assert!(rows
        .iter()
        .all(|row| row.proof_sha256 == *expected_proof_sha256));
    task6_assert_peak_determinism(&rows, "baseline");
    task6_assert_peak_determinism(&rows, "new");
    task6_assert_maxima_nonincrease(&rows);
    let distinct_proof_sha256_count = rows
        .iter()
        .map(|row| row.proof_sha256.as_str())
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let proof_execution_count = excluded_warmup_count + rows.len();
    let fixture_trace_len_log_2 = prepared_fixture_trace_len.trailing_zeros();

    let manifest = serde_json::json!({
        "schema_version": TASK6_EXACT_MEMORY_SCHEMA_VERSION,
        "artifact_head": artifact_head,
        "artifact_tree": artifact_tree,
        "release_executable": release_executable,
        "release_executable_sha256": release_executable_sha256,
        "workload_source": TASK6_WORKLOAD_SOURCE,
        "workload_id": workload_id,
        "fixture_layout": TASK6_FIXTURE_LAYOUT_PATH,
        "fixture_layout_sha256": fixture_layout_sha256,
        "fixture_layout_declared_trace_len": task6_checked_u64(
            fixture_layout_declared_trace_len,
            "fixture_layout_declared_trace_len",
        ),
        "prepared_fixture_trace_len": task6_checked_u64(
            prepared_fixture_trace_len,
            "prepared_fixture_trace_len",
        ),
        "fixture_binary": TASK6_FIXTURE_BINARY_PATH,
        "fixture_binary_sha256": fixture_binary_sha256,
        "fixture_text": TASK6_FIXTURE_TEXT_PATH,
        "fixture_text_sha256": fixture_text_sha256,
        "fixture_non_determinism_words": TASK6_FIXTURE_NON_DETERMINISM_WORDS,
        "fixture_trace_len_log_2": fixture_trace_len_log_2,
        "fixture_final_trace_size_log_2": fixture.base.final_trace_size_log_2,
        "fixture_security_level": format!("{:?}", fixture.base.prover_config.security_level),
        "selected_test_count": 1,
        "cold_preflight_count": cold_preflight_count,
        "excluded_warmup_count": excluded_warmup_count,
        "measured_row_count": rows.len(),
        "proof_execution_count": proof_execution_count,
        "matched_cpu_reference_proof_count": matched_cpu_reference_proof_count,
        "distinct_proof_sha256_count": distinct_proof_sha256_count,
        "counterbalanced_order": "A,B,B,A x 3",
        "host_acceptance_interval": "before_preflight_and_transfers_through_finish",
        "host_acceptance_time_unit": "integer_nanoseconds",
        "allocator_block_log_size": TASK6_ALLOCATOR_BLOCK_LOG_SIZE,
        "max_device_allocation_blocks_count": TASK6_MAX_DEVICE_BLOCKS,
        "actual_device_arena_bytes": actual_device_arena_bytes,
        "small_allocator_enabled": true,
        "small_allocator_log_chunk_size": TASK6_SMALL_ALLOCATOR_LOG_CHUNK_SIZE,
        "small_allocator_pool_blocks": TASK6_SMALL_ALLOCATOR_POOL_BLOCKS,
    });
    serde_json::to_writer_pretty(
        std::fs::File::create(output_root.join("manifest.json")).unwrap(),
        &manifest,
    )
    .unwrap();
    let mut raw_rows =
        std::io::BufWriter::new(std::fs::File::create(output_root.join("raw-rows.jsonl")).unwrap());
    for row in &rows {
        serde_json::to_writer(&mut raw_rows, row).unwrap();
        raw_rows.write_all(b"\n").unwrap();
    }
    raw_rows.flush().unwrap();
    let proofs = rows
        .iter()
        .map(|row| format!("{} {} {}", row.sample_index, row.arm, row.proof_sha256))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(output_root.join("proofs.sha256"), format!("{proofs}\n")).unwrap();
    let cpu_reference_parity = format!(
        "matched_cpu_reference_proof_count={matched_cpu_reference_proof_count}\n\
         measured_row_count={}\n\
         distinct_proof_sha256_count={distinct_proof_sha256_count}\n",
        rows.len(),
    );
    std::fs::write(
        output_root.join("cpu-reference-parity.log"),
        cpu_reference_parity,
    )
    .unwrap();
    serde_json::to_writer_pretty(
        std::fs::File::create(output_root.join("device-census.json")).unwrap(),
        &device_census,
    )
    .unwrap();
}

// ---------------------------------------------------------------------------
// Generic test bodies
// ---------------------------------------------------------------------------

#[test]
fn cpu_task7_dr_tail_arm_controls_are_distinct_and_complete() {
    let production = Task7DrTailArm::CompleteNewChain.backward_options();
    let legacy = Task7DrTailArm::LegacyDiagnostic.backward_options();

    assert!(production.dr_tail_megakernel);
    assert!(production.windowed_dr);
    assert!(production.windowed_dr_continuations);
    assert!(production.windowed_main_continuations);
    assert!(!legacy.dr_tail_megakernel);
    assert!(!legacy.windowed_dr);
    assert!(!legacy.windowed_dr_continuations);
    assert!(legacy.windowed_main_continuations);
    assert_ne!(production, legacy);
}

#[test]
fn cpu_task7_selected_matrix_contains_the_census_mismatch_layout() {
    let (mismatch_layout, _, canonical, raw_lookup) =
        gpu_gkr::backward::dr_tail_first_order_mismatch();
    assert_ne!(canonical, raw_lookup);
    assert!(task7_selected_layouts()
        .iter()
        .any(|path| std::path::Path::new(path).file_name().unwrap() == mismatch_layout));
}

#[test]
fn cpu_task7_production_operation_trace_is_exact() {
    let mut trace = Vec::new();
    for operation in TASK7_EXPECTED_OPERATION_TRACE {
        record_task7_operation(&mut trace, operation);
    }
    assert_eq!(trace, TASK7_EXPECTED_OPERATION_TRACE);
}

#[test]
#[should_panic(expected = "accepted stream order")]
fn cpu_task7_production_operation_trace_rejects_reordering() {
    let mut trace = vec![Task7ProofOperation::ResourcePreflight];
    record_task7_operation(&mut trace, Task7ProofOperation::ProveEnqueue);
}

fn task7_selected_layouts() -> [&'static str; 12] {
    [
        BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        SHIFT_BINOP_LAYOUT_PATH,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        MEM_WORD_ONLY_LAYOUT_PATH,
        MEM_SUBWORD_ONLY_LAYOUT_PATH,
        BIGINT_DELEGATION_LAYOUT_PATH,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        TASK6_FIXTURE_LAYOUT_PATH,
        "cs/compiled_circuits/inits_and_teardowns_layout_gkr.json",
    ]
}

pub(super) fn assert_task7_execution(evidence: &Task7ExecutionEvidence, layout_path: &str) {
    evidence.assert_complete();
    if evidence.arm == Task7DrTailArm::CompleteNewChain {
        let unique_layers = evidence
            .megakernel_coordinates
            .iter()
            .map(|coordinate| coordinate.layer_idx)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            unique_layers.len(),
            evidence.megakernel_coordinates.len(),
            "production must dispatch the DR-tail megakernel exactly once per layer"
        );
        for coordinate in &evidence.megakernel_coordinates {
            assert!(coordinate.folding_steps > coordinate.entry_round);
            assert!(coordinate.canonical_source_count > 0);
            eprintln!(
                "Task 7 megakernel dispatched: layer={} folding_steps={} entry_round={} canonical_sources={}",
                coordinate.layer_idx,
                coordinate.folding_steps,
                coordinate.entry_round,
                coordinate.canonical_source_count,
            );
        }
        let (mismatch_layout, mismatch_layer, canonical, raw_lookup) =
            gpu_gkr::backward::dr_tail_first_order_mismatch();
        assert_ne!(
            canonical, raw_lookup,
            "the census mismatch control is vacuous"
        );
        if std::path::Path::new(layout_path).file_name().unwrap() == mismatch_layout {
            assert!(
                evidence
                    .megakernel_coordinates
                    .iter()
                    .any(|coordinate| coordinate.layer_idx == mismatch_layer),
                "the canonical/raw mismatch layer must reach the production megakernel"
            );
        }
    }
}

/// Full GPU proof == CPU reference on the complete production DR chain and an
/// explicitly forced whole-layer legacy diagnostic control.
pub(super) fn run_proof_parity(fixture: &BasicUnrolledProofFixture, layout_path: &str) {
    let (production, _ms, production_evidence) = fixture
        .schedule_task7_prove(Task7DrTailArm::CompleteNewChain)
        .unwrap()
        .finish()
        .unwrap();
    assert_task7_execution(&production_evidence, layout_path);
    assert_gkr_proof_eq_for_test(&production, &fixture.expected_cpu_proof);

    let (legacy, _ms, legacy_evidence) = fixture
        .schedule_task7_prove(Task7DrTailArm::LegacyDiagnostic)
        .unwrap()
        .finish()
        .unwrap();
    assert_task7_execution(&legacy_evidence, layout_path);
    assert_gkr_proof_eq_for_test(&legacy, &fixture.expected_cpu_proof);
    assert_serialized_proof_bytes_eq(&production, &legacy);
}

/// Two concurrently-scheduled proofs on a recycled-block arena (the
/// uninitialized-witness regression guard). schedule -> schedule -> finish -> finish.
///
/// The first job takes the complete production chain and the second the forced
/// whole-layer legacy diagnostic. Both are compared against the CPU fixture and
/// their serialized bytes against each other.
pub(super) fn run_multi_schedule(fixture: &BasicUnrolledProofFixture, layout_path: &str) {
    let baseline = fixture.base.context.get_used_mem_current();
    let job0 = fixture
        .schedule_task7_prove(Task7DrTailArm::CompleteNewChain)
        .unwrap();
    let job1 = fixture
        .schedule_task7_prove(Task7DrTailArm::LegacyDiagnostic)
        .unwrap();
    let (p0, ms0, evidence0) = job0.finish().unwrap();
    eprintln!("proof_job_0 proof time: {ms0} ms");
    assert_task7_execution(&evidence0, layout_path);
    assert_gkr_proof_eq_for_test(&p0, &fixture.expected_cpu_proof);
    let (p1, ms1, evidence1) = job1.finish().unwrap();
    eprintln!("proof_job_1 proof time: {ms1} ms");
    assert_task7_execution(&evidence1, layout_path);
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
    dimension_reducing_layer_count: usize,
    dr_prepared_layer_count: usize,
    dr_prepared_bundle_final_log: Option<u32>,
    dr_plan_identity: Option<serde_json::Value>,
    dr_work: serde_json::Value,
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
    if baseline.schema_version != 3 || new.schema_version != 3 {
        return Err("Task 8 row has an unsupported schema version".to_owned());
    }
    if baseline.harness_contract != "main-dr-integrated-production-vs-whole-legacy-v1"
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
        || !baseline
            .backward_options
            .contains("dr_tail_megakernel: false")
        || !baseline.backward_options.contains("windowed_dr: false")
        || !baseline
            .backward_options
            .contains("windowed_dr_continuations: false")
        || !new.backward_options.contains("dr_tail_megakernel: true")
        || !new.backward_options.contains("windowed_dr: true")
        || !new
            .backward_options
            .contains("windowed_dr_continuations: true")
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
    validate_task8_joined_dr_work(baseline, new)?;
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
fn validate_task8_joined_dr_work(
    baseline: &Task8ExactMemoryRecord,
    new: &Task8ExactMemoryRecord,
) -> Result<(), String> {
    if baseline.dimension_reducing_layer_count == 0
        || baseline.dimension_reducing_layer_count != new.dimension_reducing_layer_count
        || baseline.dr_prepared_layer_count != 0
        || baseline.dr_prepared_bundle_final_log.is_some()
        || baseline.dr_plan_identity.is_some()
        || new.dr_prepared_layer_count != new.dimension_reducing_layer_count
        || new.dr_prepared_bundle_final_log != Some(new.final_trace_size_log_2)
    {
        return Err("Task 8 paired rows have invalid DR admission/coverage identity".to_owned());
    }
    let baseline_work = baseline
        .dr_work
        .as_array()
        .ok_or_else(|| "Task 8 legacy DR work is not an array".to_owned())?;
    let new_work = new
        .dr_work
        .as_array()
        .ok_or_else(|| "Task 8 production DR work is not an array".to_owned())?;
    if baseline_work.len() != baseline.dimension_reducing_layer_count
        || new_work.len() != new.dimension_reducing_layer_count
    {
        return Err("Task 8 DR work count differs from scheduled layer count".to_owned());
    }
    let identity = new
        .dr_plan_identity
        .as_ref()
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| "Task 8 production DR plan identity is absent".to_owned())?;
    if identity
        .get("admitted")
        .and_then(serde_json::Value::as_bool)
        != Some(true)
        || identity.get("entry").and_then(serde_json::Value::as_str) != Some("portable")
    {
        return Err("Task 8 production DR plan is not the admitted portable plan".to_owned());
    }
    let planned_layers = identity
        .get("layers")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "Task 8 production DR plan layers are absent".to_owned())?;
    if planned_layers.len() != new_work.len() {
        return Err("Task 8 admitted and scheduled DR layer counts differ".to_owned());
    }
    for (coordinate, ((legacy, production), planned)) in baseline_work
        .iter()
        .zip(new_work)
        .zip(planned_layers)
        .enumerate()
    {
        let field = |value: &serde_json::Value, name: &str| value.get(name).cloned();
        for name in [
            "coordinate",
            "kind",
            "layer_idx",
            "folding_steps",
            "canonical_source_count",
        ] {
            if field(legacy, name) != field(production, name) {
                return Err(format!(
                    "Task 8 DR coordinate {coordinate} changes {name} between arms"
                ));
            }
        }
        if legacy.get("executor").and_then(serde_json::Value::as_str) != Some("per_round")
            || legacy.get("entry_round") != Some(&serde_json::Value::Null)
            || production
                .get("executor")
                .and_then(serde_json::Value::as_str)
                != Some("mega_dr")
        {
            return Err(format!(
                "Task 8 DR coordinate {coordinate} did not execute legacy/production paths"
            ));
        }
        let entry = production
            .get("entry_round")
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| format!("Task 8 DR coordinate {coordinate} has no entry round"))?;
        if planned
            .get("entry_round")
            .and_then(serde_json::Value::as_u64)
            != Some(entry)
            || planned.get("layer_idx") != production.get("layer_idx")
            || planned.get("folding_steps") != production.get("folding_steps")
            || planned
                .get("canonical_sources")
                .and_then(serde_json::Value::as_array)
                .map(Vec::len)
                != production
                    .get("canonical_source_count")
                    .and_then(serde_json::Value::as_u64)
                    .map(|count| count as usize)
        {
            return Err(format!(
                "Task 8 DR coordinate {coordinate} differs from its admitted plan"
            ));
        }
        for (arm, work) in [("legacy", legacy), ("production", production)] {
            if work
                .get("segments")
                .and_then(serde_json::Value::as_array)
                .is_none_or(Vec::is_empty)
            {
                return Err(format!(
                    "Task 8 {arm} DR coordinate {coordinate} has empty scheduled work"
                ));
            }
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
        schema_version: 3,
        harness_contract: "main-dr-integrated-production-vs-whole-legacy-v1".to_owned(),
        artifact_head: "head".to_owned(),
        artifact_tree: "tree".to_owned(),
        release_executable: "/durable/test-binary".to_owned(),
        workload_id: "mutation".to_owned(),
        sample_index: 0,
        pair_index: 0,
        order_in_pair: 0,
        arm: "legacy".to_owned(),
        backward_options: "GkrBackwardOptions { dr_tail_megakernel: false, windowed_r0: false, windowed_main_continuations: false, windowed_dr: false, windowed_dr_continuations: false }".to_owned(),
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
        dimension_reducing_layer_count: 1,
        dr_prepared_layer_count: 0,
        dr_prepared_bundle_final_log: None,
        dr_plan_identity: None,
        dr_work: serde_json::json!([{
            "coordinate": 0,
            "kind": "dim_reducing",
            "layer_idx": 4,
            "folding_steps": 23,
            "canonical_source_count": 1,
            "executor": "per_round",
            "entry_round": null,
            "segments": ["legacy_round_0"],
        }]),
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
    record.backward_options = "GkrBackwardOptions { dr_tail_megakernel: true, windowed_r0: true, windowed_main_continuations: true, windowed_dr: true, windowed_dr_continuations: true }".to_owned();
    record.selected_strategy = "WindowedR0".to_owned();
    record.main_r0_launch_count = 1;
    record.main_continuation_planned_window_count = 1;
    record.main_tail_launch_count = 1;
    record.legacy_layer_count = 0;
    record.legacy_round_count = 0;
    record.dr_prepared_layer_count = 1;
    record.dr_prepared_bundle_final_log = Some(24);
    record.dr_plan_identity = Some(serde_json::json!({
        "admitted": true,
        "entry": "portable",
        "layers": [{
            "layer_idx": 4,
            "folding_steps": 23,
            "canonical_sources": ["GKRAddress(0)"],
            "entry_round": 15,
        }],
    }));
    record.dr_work = serde_json::json!([{
        "coordinate": 0,
        "kind": "dim_reducing",
        "layer_idx": 4,
        "folding_steps": 23,
        "canonical_source_count": 1,
        "executor": "mega_dr",
        "entry_round": 15,
        "segments": ["r0", "continuation_0", "mega_tail"],
    }]);
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

    let mut mutated = production.clone();
    mutated.main_tail_launch_count = 0;
    assert!(compare_task8_exact_memory(&baseline, &mutated)
        .unwrap_err()
        .contains("planned work counts"));

    let mutation = |mut record: Task8ExactMemoryRecord,
                    mutate: &dyn Fn(&mut Task8ExactMemoryRecord)| {
        mutate(&mut record);
        compare_task8_exact_memory(&baseline, &record).unwrap_err()
    };
    let error = mutation(production.clone(), &|row| {
        row.dr_work[0]["executor"] = serde_json::json!("per_round");
    });
    assert!(
        error.contains("did not execute legacy/production paths"),
        "{error}"
    );
    let error = mutation(production.clone(), &|row| {
        row.dr_work[0]["entry_round"] = serde_json::json!(12);
    });
    assert!(error.contains("differs from its admitted plan"), "{error}");
    let error = mutation(production.clone(), &|row| {
        row.dr_prepared_layer_count = 0;
    });
    assert!(error.contains("DR admission/coverage identity"), "{error}");
    let error = mutation(production.clone(), &|row| {
        row.dr_plan_identity = None;
    });
    assert!(
        error.contains("production DR plan identity is absent"),
        "{error}"
    );

    let mut legacy_mutated = baseline.clone();
    legacy_mutated.dr_work[0]["segments"] = serde_json::json!([]);
    let error = compare_task8_exact_memory(&legacy_mutated, &production).unwrap_err();
    assert!(
        error.contains("legacy DR coordinate 0 has empty scheduled work"),
        "{error}"
    );
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
    run_proof_parity(
        &prepare_basic_unrolled_proof_fixture_sec100(),
        BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_add_sub_multi_schedule_test() {
    run_multi_schedule(
        &prepare_basic_unrolled_proof_fixture(),
        BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_jump_branch_slt_proof_fixture(),
        JUMP_BRANCH_SLT_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_jump_branch_slt_multi_schedule_test() {
    run_multi_schedule(
        &prepare_jump_branch_slt_proof_fixture(),
        JUMP_BRANCH_SLT_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_shift_binop_proof_fixture(),
        SHIFT_BINOP_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_shift_binop_multi_schedule_test() {
    run_multi_schedule(
        &prepare_shift_binop_proof_fixture(),
        SHIFT_BINOP_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_mul_div_proof_fixture(),
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_mul_div_multi_schedule_test() {
    run_multi_schedule(
        &prepare_mul_div_proof_fixture(),
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_load_store_word_only_proof_fixture(),
        MEM_WORD_ONLY_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_load_store_word_only_multi_schedule_test() {
    run_multi_schedule(
        &prepare_load_store_word_only_proof_fixture(),
        MEM_WORD_ONLY_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_load_store_subword_only_proof_fixture(),
        MEM_SUBWORD_ONLY_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_load_store_subword_only_multi_schedule_test() {
    run_multi_schedule(
        &prepare_load_store_subword_only_proof_fixture(),
        MEM_SUBWORD_ONLY_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_bigint_proof_fixture(),
        BIGINT_DELEGATION_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_bigint_multi_schedule_test() {
    run_multi_schedule(
        &prepare_bigint_proof_fixture(),
        BIGINT_DELEGATION_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_keccak_special5_proof_fixture(),
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_keccak_special5_multi_schedule_test() {
    run_multi_schedule(
        &prepare_keccak_special5_proof_fixture(),
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_blake2_with_compression_proof_fixture(),
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_blake2_with_compression_multi_schedule_test() {
    run_multi_schedule(
        &prepare_blake2_with_compression_proof_fixture(),
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
    );
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
    run_proof_parity(
        &prepare_blake2_g_function_proof_fixture(),
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
    );
}

#[test]
#[ignore]
fn run_blake2_g_function_multi_schedule_test() {
    run_multi_schedule(
        &prepare_blake2_g_function_proof_fixture(),
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
    );
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
    run_proof_parity(&prepare_unified_proof_fixture(), TASK6_FIXTURE_LAYOUT_PATH);
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
    let proof_job_0 = fixture
        .schedule_task7_prove(Task7DrTailArm::CompleteNewChain)
        .unwrap();
    let proof_job_1 = fixture
        .schedule_task7_prove(Task7DrTailArm::LegacyDiagnostic)
        .unwrap();

    let (gpu_proof_0, proof_time_ms_0, evidence_0) = proof_job_0.finish().unwrap();
    eprintln!("unified proof_job_0 proof time: {proof_time_ms_0} ms");
    assert_task7_execution(&evidence_0, TASK6_FIXTURE_LAYOUT_PATH);
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
    // The concurrently-scheduled second proof must be bit-exact too (this is the
    // one that ran on recycled blocks) and device memory must return to baseline.
    let (gpu_proof_1, proof_time_ms_1, evidence_1) = proof_job_1.finish().unwrap();
    eprintln!("unified proof_job_1 proof time: {proof_time_ms_1} ms");
    assert_task7_execution(&evidence_1, TASK6_FIXTURE_LAYOUT_PATH);
    assert_gkr_proof_eq_for_test(&gpu_proof_1, &fixture.expected_cpu_proof);
    assert_serialized_proof_bytes_eq(&gpu_proof_0, &gpu_proof_1);
    drop(gpu_proof_0);
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
    run_proof_parity(
        &prepare_inits_and_teardowns_matrix_proof_fixture(),
        "cs/compiled_circuits/inits_and_teardowns_layout_gkr.json",
    );
}

#[test]
#[ignore]
fn run_inits_and_teardowns_multi_schedule_test() {
    run_multi_schedule(
        &prepare_inits_and_teardowns_matrix_proof_fixture(),
        "cs/compiled_circuits/inits_and_teardowns_layout_gkr.json",
    );
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
                dr_tail_megakernel: true,
                windowed_r0: true,
                windowed_main_continuations: true,
                windowed_dr: true,
                windowed_dr_continuations: true,
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
        schema_version: 3,
        harness_contract: "main-dr-integrated-production-vs-whole-legacy-v1".to_owned(),
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
        dimension_reducing_layer_count: output.dimension_reducing_layer_count,
        dr_prepared_layer_count: output.dr_prepared_layer_count,
        dr_prepared_bundle_final_log: output.dr_prepared_bundle_final_log,
        dr_plan_identity: output.dr_plan_identity,
        dr_work: output.dr_work,
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

/// Production-shaped, same-binary joined MAIN+DR acceptance harness.
///
/// This selector is intentionally ignored and may run only through the frozen
/// packet. It performs two excluded warmups (whole legacy then joined production) followed
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
                assert_exact_bytes_eq_for_test(
                    &first_proof,
                    &second_proof,
                    &format!("{workload_id} pair {pair_index} proof bytes"),
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
