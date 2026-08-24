use super::*;
use gpu_gkr::BackwardExecutionStrategy;
use serde::Serialize;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

const TASK6_EXACT_MEMORY_SCHEMA_VERSION: u32 = 1;
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
        require_exact_memory_equal(field, start, returned)?;
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
fn cpu_exact_memory_comparator_rejects_each_positive_byte_delta() {
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
fn cpu_exact_memory_comparator_rejects_hidden_small_pool_growth() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    let mut new = task6_exact_memory_record_for_test("new");
    new.backward_peak_logical_live_bytes += 1;
    let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
    assert_eq!(error.field, "backward.logical_live_peak_bytes");
}

#[test]
fn cpu_exact_memory_comparator_rejects_whole_peak_masking() {
    let baseline = task6_exact_memory_record_for_test("baseline");
    let mut new = task6_exact_memory_record_for_test("new");
    new.backward_peak_physical_backing_bytes += 1;
    let error = compare_task6_exact_memory_pair(&baseline, &new).unwrap_err();
    assert_eq!(error.field, "backward.physical_backing_peak_bytes");
}

#[test]
fn cpu_exact_memory_record_is_raw_integer_bytes() {
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
fn cpu_exact_memory_record_rejects_entry_config_and_return_drift() {
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

struct Task6MeasuredProofJob<'context> {
    job: GpuGKRProofJob<'static, Global>,
    backward: crate::proof::ProofMemoryHighWaterSink<'context>,
    whole: gpu_prover_context::DeviceMemoryHighWaterObserver<'context>,
    sequence: Arc<AtomicUsize>,
    whole_start_sequence: usize,
    host_start: Instant,
}

struct Task6MeasuredProof {
    proof: GKRProof<BF, E4, DefaultTreeConstructor>,
    proof_time_ms: u64,
    cuda_proof_time_ms: f32,
    backward: gpu_prover_context::PoolMemoryHighWaterReport,
    whole: gpu_prover_context::PoolMemoryHighWaterReport,
    legacy_dr_execution_count: usize,
    dr_prepared_layer_count: usize,
    dr_bundle_final_log: Option<u32>,
}

impl Task6MeasuredProofJob<'_> {
    fn finish(self) -> CudaResult<Task6MeasuredProof> {
        let (proof, cuda_proof_time_ms) = self.job.finish()?;
        let job_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);
        let backward = self.backward.finish();
        let backward_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);
        let whole = self.whole.finish();
        let whole_finish_sequence = self.sequence.fetch_add(1, Ordering::SeqCst);

        assert!(self.whole_start_sequence < backward.start_sequence);
        assert!(backward.start_sequence < backward.seal_sequence);
        assert!(backward.seal_sequence < job_finish_sequence);
        assert!(job_finish_sequence < backward_finish_sequence);
        assert!(backward_finish_sequence <= whole_finish_sequence);

        Ok(Task6MeasuredProof {
            proof,
            proof_time_ms: self.host_start.elapsed().as_millis().try_into().unwrap(),
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
    fn schedule_task6_exact_memory_prove(
        &self,
        backward_options: GkrBackwardOptions,
    ) -> CudaResult<Task6MeasuredProofJob<'_>> {
        let sequence = Arc::new(AtomicUsize::new(0));
        let whole = self.context.observe_device_memory_high_water();
        let whole_start_sequence = sequence.fetch_add(1, Ordering::SeqCst);
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

        let mem_before_prove = self.context.get_device_memory_usage();
        let mut backward = crate::proof::ProofMemoryHighWaterSink::new(Arc::clone(&sequence));
        let host_start = Instant::now();
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
        ..GkrBackwardOptions::default()
    };
    let new_options = GkrBackwardOptions {
        windowed_dr: true,
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
