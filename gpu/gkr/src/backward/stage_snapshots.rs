use std::collections::BTreeMap;

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
use std::sync::{Arc, Mutex};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use super::kernels::{ClaimBufferLayout, DeviceClaimPointAndBatching};
use crate::upstream::GKRAddress;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq)]
pub struct GKRBackwardStageSnapshot {
    pub layer_idx: usize,
    pub claim_point: Vec<E4>,
    pub batching_challenge: E4,
    pub claims: BTreeMap<GKRAddress, E4>,
}

#[doc(hidden)]
pub struct GKRBackwardStageSnapshotSink {
    snapshots: Vec<GKRBackwardStageSnapshot>,
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    capture_snapshots: bool,
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    task8_request: Option<Arc<Task8ContinuationDifferentialState>>,
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    task8_execution_counts: Option<Arc<Mutex<Task8ExecutionCountsState>>>,
    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    task8_requests_taken: bool,
}

impl Default for GKRBackwardStageSnapshotSink {
    fn default() -> Self {
        Self {
            snapshots: Vec::new(),
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            capture_snapshots: true,
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            task8_request: None,
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            task8_execution_counts: None,
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            task8_requests_taken: false,
        }
    }
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationDifferentialReport {
    pub non_identity_coordinates: usize,
    pub layers: usize,
    pub coordinates: usize,
    pub folding_steps: Vec<usize>,
    pub start_rounds: Vec<usize>,
    pub masks: Vec<u16>,
    pub max_sources: usize,
    pub max_legacy_displacement: usize,
    pub semantic_comparisons: usize,
    pub publication_elements_compared: usize,
    pub comparator_field_coverage_checks: usize,
    pub mutation_checks: usize,
    pub source_table_identity_rows: usize,
    pub source_identity_records: usize,
    pub source_id_census: Vec<(usize, Vec<u32>)>,
    pub source_backing_census: Vec<(usize, usize)>,
    pub allocation_records: usize,
    pub topology_owner_records: usize,
    pub topology_owner_kinds: Vec<String>,
    pub topology_coordinates: usize,
    pub later_start_shared_prior_coordinates: usize,
    pub multi_source_coordinates: usize,
    pub arm_memory_comparisons: usize,
    pub procedural_source_records: usize,
    pub mutation_families: Vec<String>,
    pub capacity_overlap_rows: usize,
    pub capacity_heavy_layers: Vec<usize>,
    pub capacity_publication_bytes: Vec<usize>,
    pub capacity_overlap_live_bytes: Vec<usize>,
    pub capacity_overlap_owner_counts: Vec<usize>,
    pub capacity_physical_peak_bytes: Vec<usize>,
    pub capacity_logical_peak_bytes: Vec<usize>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[doc(hidden)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MainContinuationExecutionCounts {
    pub layers: usize,
    pub window_launches: usize,
    pub legacy_remainder_rounds: usize,
    pub legacy_full_rounds: usize,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[derive(Default)]
struct Task8ExecutionCountsState {
    counts: MainContinuationExecutionCounts,
    finalized: bool,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[doc(hidden)]
pub struct MainContinuationExecutionCountsHandle {
    state: Arc<Mutex<Task8ExecutionCountsState>>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
impl MainContinuationExecutionCountsHandle {
    pub fn finish(self) -> MainContinuationExecutionCounts {
        let state = self
            .state
            .lock()
            .expect("Task 8 execution-count mutex poisoned");
        assert!(
            state.finalized,
            "Task 8 execution counts were not finalized by the backward scheduler"
        );
        state.counts.clone()
    }
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
struct Task8ContinuationDifferentialState {
    report: Mutex<Option<Result<MainContinuationDifferentialReport, String>>>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[doc(hidden)]
#[derive(Clone)]
pub struct MainContinuationDifferentialHandle {
    state: Arc<Task8ContinuationDifferentialState>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
impl MainContinuationDifferentialHandle {
    pub fn finish(self) -> Result<MainContinuationDifferentialReport, String> {
        self.state
            .report
            .lock()
            .expect("Task 8 differential report mutex poisoned")
            .take()
            .expect("Task 8 differential probe did not publish a terminal report")
    }
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[derive(Clone)]
pub(crate) struct Task8ContinuationDifferentialRequest {
    state: Arc<Task8ContinuationDifferentialState>,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
impl Task8ContinuationDifferentialRequest {
    pub(crate) fn publish(self, report: Result<MainContinuationDifferentialReport, String>) {
        if let Ok(report) = report.as_ref() {
            assert!(
                report.coordinates > 0,
                "Task 8 differential ran zero coordinates"
            );
            assert!(
                !report.start_rounds.is_empty(),
                "Task 8 differential observed no continuation start rounds"
            );
            assert!(
                !report.masks.is_empty(),
                "Task 8 differential observed no program masks"
            );
            assert!(
                report.semantic_comparisons > 0,
                "Task 8 differential performed zero semantic comparisons"
            );
            assert_eq!(
                report.semantic_comparisons,
                report.publication_elements_compared + 26 * report.topology_coordinates,
                "Task 8 semantic comparison census omitted a live field"
            );
            assert_eq!(
                report.comparator_field_coverage_checks,
                24 * report.topology_coordinates,
                "Task 8 comparator field-coverage census omitted a field"
            );
            assert_eq!(
                report.source_table_identity_rows, report.layers,
                "Task 8 did not bind every legacy compiler source table to the window table"
            );
            assert!(
                report.source_identity_records > 0,
                "Task 8 differential retained no production source identities"
            );
            assert!(
                report.allocation_records > 0,
                "Task 8 differential retained no live allocation topology"
            );
            assert_eq!(report.source_id_census.len(), report.layers);
            assert_eq!(report.source_backing_census.len(), report.layers);
            assert!(report.topology_owner_records > report.allocation_records);
            assert!(!report.topology_owner_kinds.is_empty());
            assert!(
                report.arm_memory_comparisons > 0,
                "Task 8 differential compared no arm high-water reports"
            );
            assert_eq!(
                report.topology_coordinates,
                report.layers * report.start_rounds.len(),
                "Task 8 live topology did not cover every layer/start coordinate"
            );
            assert_eq!(
                report.later_start_shared_prior_coordinates,
                report.topology_coordinates - report.layers,
                "Task 8 later-start shared-prior limitation census drifted"
            );
            assert_eq!(
                report.mutation_checks,
                16 * report.layers
                    + 22 * report.later_start_shared_prior_coordinates
                    + 2 * report.multi_source_coordinates,
                "Task 8 live mutation census omitted or invented a mutation"
            );
            assert_eq!(
                report.arm_memory_comparisons,
                2 * report.topology_coordinates,
                "Task 8 did not compare both direct arm peak metrics"
            );
            assert!(
                !report.mutation_families.is_empty(),
                "Task 8 retained no named mutation families"
            );
            assert_eq!(
                report.capacity_overlap_rows, report.layers,
                "Task 8 did not observe one first-pass P+P/2 overlap per layer"
            );
            assert_eq!(
                report.capacity_publication_bytes.len(),
                report.capacity_heavy_layers.len(),
                "Task 8 capacity evidence lost its heavy-row identity"
            );
            assert_eq!(
                report.capacity_publication_bytes.len(),
                report.capacity_overlap_live_bytes.len(),
                "Task 8 capacity evidence lost its real P+P/2 overlap"
            );
            assert_eq!(
                report.capacity_publication_bytes.len(),
                report.capacity_overlap_owner_counts.len(),
                "Task 8 capacity evidence lost its real owner count"
            );
            assert_eq!(
                report.capacity_publication_bytes.len(),
                report.capacity_physical_peak_bytes.len(),
                "Task 8 capacity evidence lost a physical peak"
            );
            assert_eq!(
                report.capacity_publication_bytes.len(),
                report.capacity_logical_peak_bytes.len(),
                "Task 8 capacity evidence lost a logical peak"
            );
        }
        let previous = self
            .state
            .report
            .lock()
            .expect("Task 8 differential report mutex poisoned")
            .replace(report);
        assert!(
            previous.is_none(),
            "Task 8 differential report published twice"
        );
    }
}

impl GKRBackwardStageSnapshotSink {
    pub fn into_snapshots(self) -> Vec<GKRBackwardStageSnapshot> {
        self.snapshots
    }

    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    #[doc(hidden)]
    pub fn requesting_main_continuation_differential() -> (Self, MainContinuationDifferentialHandle)
    {
        let state = Arc::new(Task8ContinuationDifferentialState {
            report: Mutex::new(None),
        });
        (
            Self {
                snapshots: Vec::new(),
                capture_snapshots: false,
                task8_request: Some(Arc::clone(&state)),
                task8_execution_counts: None,
                task8_requests_taken: false,
            },
            MainContinuationDifferentialHandle { state },
        )
    }

    #[cfg(all(
        any(test, feature = "task8_continuation_differential_test"),
        not(no_cuda)
    ))]
    #[doc(hidden)]
    pub fn requesting_main_continuation_execution_counts(
    ) -> (Self, MainContinuationExecutionCountsHandle) {
        let state = Arc::new(Mutex::new(Task8ExecutionCountsState::default()));
        (
            Self {
                snapshots: Vec::new(),
                capture_snapshots: false,
                task8_request: None,
                task8_execution_counts: Some(Arc::clone(&state)),
                task8_requests_taken: false,
            },
            MainContinuationExecutionCountsHandle { state },
        )
    }
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) struct Task8SinkRequests {
    pub(crate) differential: Option<Task8ContinuationDifferentialRequest>,
    execution_counts: Option<Arc<Mutex<Task8ExecutionCountsState>>>,
    pub(crate) capture_snapshots: bool,
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
impl Task8SinkRequests {
    pub(crate) fn tracks_execution_counts(&self) -> bool {
        self.execution_counts.is_some()
    }

    pub(crate) fn record_main_layer(
        &self,
        window_launches: usize,
        legacy_remainder_rounds: usize,
        legacy_full_rounds: usize,
    ) {
        if let Some(state) = self.execution_counts.as_ref() {
            let mut state = state.lock().expect("Task 8 execution-count mutex poisoned");
            assert!(
                !state.finalized,
                "Task 8 execution counts already finalized"
            );
            state.counts.layers += 1;
            state.counts.window_launches += window_launches;
            state.counts.legacy_remainder_rounds += legacy_remainder_rounds;
            state.counts.legacy_full_rounds += legacy_full_rounds;
        }
    }

    pub(crate) fn finalize_execution_counts(&self) {
        if let Some(state) = self.execution_counts.as_ref() {
            let mut state = state.lock().expect("Task 8 execution-count mutex poisoned");
            assert!(!state.finalized, "Task 8 execution counts finalized twice");
            state.finalized = true;
        }
    }
}

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) unsafe fn take_task8_sink_requests(
    sink: UnsafeMutAccessor<GKRBackwardStageSnapshotSink>,
) -> Task8SinkRequests {
    // SAFETY: the scheduler calls this once, before it schedules the first
    // callback that receives `sink`. The request is ordinary Box-owned host
    // metadata, not pool-backed memory, and no stream operation can yet alias
    // this field. All later access is through the cloned `Arc` request state.
    let sink = unsafe { sink.get_mut() };
    assert!(
        !std::mem::replace(&mut sink.task8_requests_taken, true),
        "Task 8 sink requests were extracted more than once or after callback scheduling"
    );
    Task8SinkRequests {
        differential: sink
            .task8_request
            .take()
            .map(|state| Task8ContinuationDifferentialRequest { state }),
        execution_counts: sink.task8_execution_counts.take(),
        capture_snapshots: sink.capture_snapshots,
    }
}

pub(super) fn schedule_stage_snapshot(
    layer_idx: usize,
    point_and_batching: &DeviceClaimPointAndBatching,
    claims: &DeviceAllocation<E4>,
    claim_layout: &ClaimBufferLayout,
    output: UnsafeMutAccessor<GKRBackwardStageSnapshotSink>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(claims.len(), claim_layout.claim_count());
    let stream = context.get_exec_stream();
    let mut point_host = unsafe { context.alloc_host_uninit_slice(point_and_batching.len()) };
    let mut claims_host = unsafe { context.alloc_host_uninit_slice(claims.len()) };
    memory_copy_async(
        &mut point_host,
        point_and_batching.slice(0, point_and_batching.len()),
        stream,
    )?;
    memory_copy_async(&mut claims_host, claims, stream)?;

    let point_host = point_host.get_accessor();
    let claims_host = claims_host.get_accessor();
    let addresses = claim_layout.addresses.clone();
    callbacks.schedule(
        move || {
            let point_and_batching = unsafe { point_host.get() };
            let (&batching_challenge, claim_point) = point_and_batching
                .split_last()
                .expect("stage snapshot must contain a batching challenge");
            let claims = addresses
                .iter()
                .copied()
                .zip(unsafe { claims_host.get() }.iter().copied())
                .collect();
            unsafe { output.get_mut() }
                .snapshots
                .push(GKRBackwardStageSnapshot {
                    layer_idx,
                    claim_point: claim_point.to_vec(),
                    batching_challenge,
                    claims,
                });
        },
        stream,
    )
}
