//! Task-8-only prepared-state differential support.
//!
//! This module is excluded from normal and `no_cuda` builds. It borrows the
//! production-owned main-entry storage and never exports that owner.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeAccessor};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{
    alloc_static_pinned_box_from_slice, alloc_static_pinned_box_uninit, StaticPinnedBox,
};
use gpu_gkr_compiler::{MainContinuationWindowProgram, SourceId};
use gpu_prover_context::PoolMemoryHighWaterReport;
use gpu_prover_context::ProverContext;

use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr,
    launch_backward_dual_finalize_from_partials, launch_build_eq_high_and_low_groups_from_point,
    make_eq_sizes, record_active_eq_slot_fold, resolve_active_eq_slot, warp_partial_count,
    GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::backward::main_continuation::abi::MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
use crate::backward::main_continuation::binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    launch_main_continuation_window, MainContinuationWindowRuntimeScratch,
};
use crate::backward::main_continuation::{ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::main_layer::execution_plan::main_continuation_post_tail_eq_boundary;
use crate::backward::stage_snapshots::{
    MainContinuationDifferentialReport, Task8ContinuationDifferentialRequest,
};
use crate::backward::vm::production_bind::{
    canonicalize_legacy_publication, family_read_place, prepare_continuation_differential_bank,
    prepare_continuation_differential_rounds, LegacyPublicationCanonicalizationError,
    Task8LivePublicationEvent,
};
use crate::backward::vm::seg::launch_bwd_seg_build_fold_weights;
use crate::backward::window::binding::window_partials_len;
use crate::backward::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::upstream::{Field, FieldExtension, GKRAddress, PrimeField};
use crate::{
    BackwardExecutionStrategy, GkrBackwardOptions, GkrPrograms, GpuGKRStorage, WindowTailArm,
};

pub(crate) const TASK8_DIAGNOSTIC: &str = "task8-main-continuation-prepared-differential-v1";

const TASK8_READBACK_CHUNK_BYTES: usize = 16 << 20;
const TASK8_NON_PUBLICATION_COMPARISONS: usize =
    12 + 3 + 8 + 1 + 1 + 2 * GKR_EQ_GROUP_TABLE_LEN * (1 + GKR_EQ_HIGH_SLOTS) + 3;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8AllocationRecord {
    kind: &'static str,
    owner: usize,
    size_bytes: usize,
    successful_requested_bytes: usize,
    physical_backing_delta_bytes: i128,
    logical_live_delta_bytes: i128,
    multiplicity: usize,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    retired: bool,
}

fn allocation_record<T>(
    kind: &'static str,
    allocation: &DeviceSlice<T>,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
) -> Task8AllocationRecord {
    let size_bytes = allocation
        .len()
        .checked_mul(std::mem::size_of::<T>())
        .expect("Task 8 allocation byte count overflowed usize");
    Task8AllocationRecord {
        kind,
        owner: allocation.as_ptr() as usize,
        size_bytes,
        successful_requested_bytes: size_bytes,
        physical_backing_delta_bytes: 0,
        logical_live_delta_bytes: 0,
        multiplicity: 1,
        live_from,
        live_until,
        overlap_group,
        placement,
        retired: true,
    }
}

fn allocation_record_with_usage<T>(
    kind: &'static str,
    allocation: &DeviceSlice<T>,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    before: gpu_prover_context::PoolMemoryUsage,
    after: gpu_prover_context::PoolMemoryUsage,
) -> Task8AllocationRecord {
    let mut record = allocation_record(
        kind,
        allocation,
        live_from,
        live_until,
        overlap_group,
        placement,
    );
    record.physical_backing_delta_bytes =
        signed_snapshot_delta(after.physical_backing_bytes, before.physical_backing_bytes);
    record.logical_live_delta_bytes =
        signed_snapshot_delta(after.logical_live_bytes, before.logical_live_bytes);
    record
}

fn allocation_group_record(
    kind: &'static str,
    owner: usize,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    multiplicity: usize,
    report: &PoolMemoryHighWaterReport,
) -> Task8AllocationRecord {
    let physical_backing_delta_bytes = signed_snapshot_delta(
        report.return_to_entry.physical_backing_bytes,
        report.start.physical_backing_bytes,
    );
    let logical_live_delta_bytes = signed_snapshot_delta(
        report.return_to_entry.logical_live_bytes,
        report.start.logical_live_bytes,
    );
    Task8AllocationRecord {
        kind,
        owner,
        size_bytes: report.summed_requested_bytes,
        successful_requested_bytes: report.summed_requested_bytes,
        physical_backing_delta_bytes,
        logical_live_delta_bytes,
        multiplicity,
        live_from,
        live_until,
        overlap_group,
        placement,
        retired: true,
    }
}

#[inline]
fn signed_snapshot_delta(after: usize, before: usize) -> i128 {
    (after as i128) - (before as i128)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8SourceFieldClass {
    Base,
    Extension,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Task8SourceSampleValues {
    Base(Vec<BF>),
    Extension(Vec<E4>),
}

struct ScheduledSourceIdentityRecord {
    source: SourceId,
    address: GKRAddress,
    field_class: Task8SourceFieldClass,
    backing_base: usize,
    view_offset: usize,
    stride_bytes: usize,
    backing_bytes: usize,
    backing_requested_bytes: usize,
    samples: ScheduledSourceSampleValues,
}

enum ScheduledSourceSampleValues {
    Base(Vec<ScheduledReadback<BF>>),
    Extension(Vec<ScheduledReadback<E4>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8SourceIdentityRecord {
    source: SourceId,
    address: GKRAddress,
    field_class: Task8SourceFieldClass,
    backing_base: usize,
    view_offset: usize,
    stride_bytes: usize,
    backing_bytes: usize,
    backing_requested_bytes: usize,
    samples: Task8SourceSampleValues,
}

impl ScheduledSourceIdentityRecord {
    fn materialize(self) -> Task8SourceIdentityRecord {
        let samples = match self.samples {
            ScheduledSourceSampleValues::Base(values) => Task8SourceSampleValues::Base(
                values
                    .into_iter()
                    .flat_map(ScheduledReadback::materialize)
                    .collect(),
            ),
            ScheduledSourceSampleValues::Extension(values) => Task8SourceSampleValues::Extension(
                values
                    .into_iter()
                    .flat_map(ScheduledReadback::materialize)
                    .collect(),
            ),
        };
        Task8SourceIdentityRecord {
            source: self.source,
            address: self.address,
            field_class: self.field_class,
            backing_base: self.backing_base,
            view_offset: self.view_offset,
            stride_bytes: self.stride_bytes,
            backing_bytes: self.backing_bytes,
            backing_requested_bytes: self.backing_requested_bytes,
            samples,
        }
    }
}

#[derive(Clone, Debug)]
struct EqObservation {
    sizes: GkrEqSizes,
    low: Vec<E4>,
    high: Vec<E4>,
}

#[derive(Clone, Debug)]
struct PreparedObservation {
    publication: Vec<E4>,
    coefficients: Vec<E4>,
    challenges: Vec<E4>,
    seed: Vec<u32>,
    claim: Vec<E4>,
    eq_prefactor: Vec<E4>,
    pre_eq: EqObservation,
    post_eq: EqObservation,
    boundary: (u8, u8, GkrEqSizes),
}

struct ScheduledReadback<T> {
    values: Arc<Mutex<Vec<T>>>,
    expected_len: usize,
}

impl<T> ScheduledReadback<T> {
    fn materialize(self) -> Vec<T> {
        let mut values = self.values.lock().expect("Task 8 readback mutex poisoned");
        assert_eq!(
            values.len(),
            self.expected_len,
            "Task 8 readback callback census is incomplete"
        );
        std::mem::take(&mut *values)
    }
}

struct ScheduledEqObservation {
    sizes: GkrEqSizes,
    low: ScheduledReadback<E4>,
    high: ScheduledReadback<E4>,
}

struct ScheduledLiveMutationEvidence {
    e4: Vec<(
        &'static str,
        Task8LiveMutationTarget,
        E4,
        ScheduledReadback<E4>,
    )>,
    u32: Vec<(
        &'static str,
        Task8LiveMutationTarget,
        u32,
        ScheduledReadback<u32>,
    )>,
    prior_original: Option<ScheduledReadback<E4>>,
}

#[derive(Clone, Copy)]
enum Task8LiveMutationTarget {
    Publication(usize),
    Coefficient(usize),
    Challenge(usize),
    Seed(usize),
    Claim(usize),
    EqPrefactor(usize),
    PostEqLow(usize),
    PriorPublication,
}

enum Task8MaterializedLiveMutation {
    E4(&'static str, Task8LiveMutationTarget, E4),
    U32(&'static str, Task8LiveMutationTarget, u32),
}

impl ScheduledLiveMutationEvidence {
    fn empty() -> Self {
        Self {
            e4: Vec::new(),
            u32: Vec::new(),
            prior_original: None,
        }
    }

    fn materialize(self) -> Vec<Task8MaterializedLiveMutation> {
        let prior_original =
            self.prior_original
                .map(ScheduledReadback::materialize)
                .map(|values| {
                    assert_eq!(values.len(), 1);
                    values[0]
                });
        let mut mutations = Vec::new();
        for (family, target, expected, values) in self.e4 {
            assert_eq!(values.materialize(), [expected]);
            if matches!(target, Task8LiveMutationTarget::PriorPublication) {
                let original = prior_original
                    .expect("Task 8 prior-cell mutation lost its pre-adoption readback");
                assert_ne!(
                    original, expected,
                    "Task 8 prior-cell mutation did not change the live prior"
                );
            }
            mutations.push(Task8MaterializedLiveMutation::E4(family, target, expected));
        }
        for (family, target, expected, values) in self.u32 {
            assert_eq!(values.materialize(), [expected]);
            mutations.push(Task8MaterializedLiveMutation::U32(family, target, expected));
        }
        mutations
    }
}

impl ScheduledEqObservation {
    fn materialize(self) -> EqObservation {
        EqObservation {
            sizes: self.sizes,
            low: self.low.materialize(),
            high: self.high.materialize(),
        }
    }
}

struct ScheduledPreparedObservation {
    publication: ScheduledReadback<E4>,
    coefficients: ScheduledReadback<E4>,
    challenges: ScheduledReadback<E4>,
    seed: ScheduledReadback<u32>,
    claim: ScheduledReadback<E4>,
    eq_prefactor: ScheduledReadback<E4>,
    pre_eq: ScheduledEqObservation,
    post_eq: ScheduledEqObservation,
    boundary: (u8, u8, GkrEqSizes),
    memory: PoolMemoryHighWaterReport,
    allocations: Vec<Task8AllocationRecord>,
    live_mutations: ScheduledLiveMutationEvidence,
}

#[derive(Clone, Debug)]
struct Task8AdoptionEvidence {
    had_prior: bool,
    input_live_before: bool,
    first_deltas: Vec<u8>,
    first_reads_only_published: bool,
    input_retired: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8AdoptionEvidenceError {
    UnexpectedPriorState,
    Delta,
    ReadSet,
    Retirement,
}

fn validate_adoption_evidence(
    evidence: &Task8AdoptionEvidence,
) -> Result<(), Task8AdoptionEvidenceError> {
    if !evidence.had_prior {
        return Ok(());
    }
    if !evidence.input_live_before {
        return Err(Task8AdoptionEvidenceError::UnexpectedPriorState);
    }
    if evidence.first_deltas.is_empty() || evidence.first_deltas.iter().any(|delta| *delta != 3) {
        return Err(Task8AdoptionEvidenceError::Delta);
    }
    if !evidence.first_reads_only_published {
        return Err(Task8AdoptionEvidenceError::ReadSet);
    }
    if !evidence.input_retired {
        return Err(Task8AdoptionEvidenceError::Retirement);
    }
    Ok(())
}

fn validate_adoption_mutations(evidence: &Task8AdoptionEvidence) -> (usize, BTreeSet<String>) {
    validate_adoption_evidence(evidence).expect("Task 8 live adoption evidence is invalid");
    if !evidence.had_prior {
        return (0, BTreeSet::new());
    }
    let mut delta = evidence.clone();
    delta.first_deltas[0] = 2;
    assert_eq!(
        validate_adoption_evidence(&delta),
        Err(Task8AdoptionEvidenceError::Delta)
    );
    let mut read_set = evidence.clone();
    read_set.first_reads_only_published = false;
    assert_eq!(
        validate_adoption_evidence(&read_set),
        Err(Task8AdoptionEvidenceError::ReadSet)
    );
    let mut retirement = evidence.clone();
    retirement.input_retired = false;
    assert_eq!(
        validate_adoption_evidence(&retirement),
        Err(Task8AdoptionEvidenceError::Retirement)
    );
    (
        3,
        ["seeded-adoption-delta-3", "zero-remainder-take"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
    )
}

impl ScheduledPreparedObservation {
    fn materialize(
        self,
    ) -> (
        PreparedObservation,
        PoolMemoryHighWaterReport,
        Vec<Task8AllocationRecord>,
        ScheduledLiveMutationEvidence,
    ) {
        (
            PreparedObservation {
                publication: self.publication.materialize(),
                coefficients: self.coefficients.materialize(),
                challenges: self.challenges.materialize(),
                seed: self.seed.materialize(),
                claim: self.claim.materialize(),
                eq_prefactor: self.eq_prefactor.materialize(),
                pre_eq: self.pre_eq.materialize(),
                post_eq: self.post_eq.materialize(),
                boundary: self.boundary,
            },
            self.memory,
            self.allocations,
            self.live_mutations,
        )
    }
}

fn upload<T: Copy>(
    context: &ProverContext,
    host: &[T],
) -> CudaResult<(DeviceAllocation<T>, StaticPinnedBox<T>)> {
    let staging = alloc_static_pinned_box_from_slice(host)?;
    let mut device = context.alloc(host.len().max(1), AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device[..host.len()],
        &staging[..],
        context.get_exec_stream(),
    )?;
    Ok((device, staging))
}

fn write_claim_point_symbol(
    context: &ProverContext,
    point: &[E4],
) -> CudaResult<StaticPinnedBox<E4>> {
    let staging = alloc_static_pinned_box_from_slice(point)?;
    // SAFETY: the main-layer claim-point symbol is sized for every admitted
    // folding width; the corpus maximum is pinned independently by preflight.
    let destination = unsafe {
        DeviceSlice::from_raw_parts_mut(get_main_layer_claim_point_device_ptr(), point.len())
    };
    memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    Ok(staging)
}

fn schedule_read_device_chunked<T>(
    source: &DeviceSlice<T>,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledReadback<T>>
where
    T: Copy + Default + Send + Sync + 'static,
{
    assert_eq!(scratch.len(), TASK8_READBACK_CHUNK_BYTES);
    assert_eq!(
        (scratch.as_ptr() as usize) % std::mem::align_of::<T>(),
        0,
        "Task 8 shared readback scratch lost type alignment"
    );
    let chunk_elements = (scratch.len() / std::mem::size_of::<T>()).max(1);
    let expected_len = source.len();
    let output = Arc::new(Mutex::new(Vec::new()));
    if source.is_empty() {
        return Ok(ScheduledReadback {
            values: output,
            expected_len: 0,
        });
    }
    let accessor = UnsafeAccessor::new(&scratch[..]);
    for offset in (0..source.len()).step_by(chunk_elements) {
        let len = chunk_elements.min(source.len() - offset);
        let byte_len = len
            .checked_mul(std::mem::size_of::<T>())
            .expect("Task 8 readback byte count overflowed usize");
        // SAFETY: the scratch base alignment is checked above and byte_len is
        // exactly `len * size_of::<T>()`.
        let host_chunk =
            unsafe { std::slice::from_raw_parts_mut(scratch.as_mut_ptr().cast::<T>(), len) };
        memory_copy_async(
            host_chunk,
            &source[offset..offset + len],
            context.get_exec_stream(),
        )?;
        let callback_output = Arc::clone(&output);
        callbacks.schedule(
            move || unsafe {
                let mut output = callback_output
                    .lock()
                    .expect("Task 8 readback mutex poisoned");
                if offset == 0 {
                    output
                        .try_reserve_exact(expected_len)
                        .unwrap_or_else(|error| {
                            panic!(
                            "Task 8 readback could not reserve {expected_len} elements: {error}"
                        )
                        });
                }
                assert_eq!(
                    output.len(),
                    offset,
                    "Task 8 chunk callbacks executed out of order"
                );
                let bytes = &accessor.get()[..byte_len];
                let values = std::slice::from_raw_parts(bytes.as_ptr().cast::<T>(), len);
                output.extend_from_slice(values);
            },
            context.get_exec_stream(),
        )?;
    }
    Ok(ScheduledReadback {
        values: output,
        expected_len,
    })
}

fn schedule_read_all_eq(
    sizes: GkrEqSizes,
    eq_low: &DeviceAllocation<E4>,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledEqObservation> {
    // SAFETY: the high Eq symbol is a contiguous two-table device region.
    let high = unsafe {
        DeviceSlice::from_raw_parts(
            get_eq_high_constant_device_ptr() as *const E4,
            GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
        )
    };
    Ok(ScheduledEqObservation {
        sizes,
        low: schedule_read_device_chunked(eq_low, scratch, callbacks, context)?,
        high: schedule_read_device_chunked(high, scratch, callbacks, context)?,
    })
}

fn deterministic_e4(tag: u32) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|lane| {
        BF::from_u32_with_reduction(tag.wrapping_mul(17).wrapping_add(lane as u32 + 1))
    }))
}

struct TranscriptBuffers {
    seed: DeviceAllocation<u32>,
    claim: DeviceAllocation<E4>,
    prefactor: DeviceAllocation<E4>,
    coefficients: DeviceAllocation<E4>,
    challenges: DeviceAllocation<E4>,
    _seed_staging: StaticPinnedBox<u32>,
    _claim_staging: StaticPinnedBox<E4>,
    _prefactor_staging: StaticPinnedBox<E4>,
    allocations: Vec<Task8AllocationRecord>,
}

fn transcript_buffers(context: &ProverContext) -> CudaResult<TranscriptBuffers> {
    let mut allocations = Vec::new();
    let seed_host = [0x1020_3040, 0x5060_7080, 1, 2, 3, 5, 8, 13];
    let before_seed = context.get_device_memory_usage();
    let (seed, seed_staging) = upload(context, &seed_host)?;
    let after_seed = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_seed",
        &seed,
        4,
        8,
        2,
        "best_fit",
        before_seed,
        after_seed,
    ));
    let before_claim = after_seed;
    let (claim, claim_staging) = upload(context, &[deterministic_e4(0x51)])?;
    let after_claim = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_claim",
        &claim,
        4,
        8,
        2,
        "best_fit",
        before_claim,
        after_claim,
    ));
    let before_prefactor = after_claim;
    let (prefactor, prefactor_staging) = upload(context, &[deterministic_e4(0x71)])?;
    let after_prefactor = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_prefactor",
        &prefactor,
        4,
        8,
        2,
        "best_fit",
        before_prefactor,
        after_prefactor,
    ));
    let before_coefficients = after_prefactor;
    let coefficients = context.alloc(12, AllocationPlacement::BestFit)?;
    let after_coefficients = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "coefficients",
        &coefficients,
        4,
        8,
        2,
        "best_fit",
        before_coefficients,
        after_coefficients,
    ));
    let before_challenges = after_coefficients;
    let challenges = context.alloc(3, AllocationPlacement::BestFit)?;
    let after_challenges = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "challenges",
        &challenges,
        4,
        8,
        2,
        "best_fit",
        before_challenges,
        after_challenges,
    ));
    Ok(TranscriptBuffers {
        seed,
        claim,
        prefactor,
        coefficients,
        challenges,
        _seed_staging: seed_staging,
        _claim_staging: claim_staging,
        _prefactor_staging: prefactor_staging,
        allocations,
    })
}

fn retain_in_callback<T: Send + Sync + 'static>(
    value: T,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    callbacks.schedule(
        move || {
            let _ = &value;
        },
        context.get_exec_stream(),
    )
}

fn schedule_live_device_mutation<T>(
    family: &'static str,
    target: Task8LiveMutationTarget,
    destination: *mut T,
    value: T,
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<(
    &'static str,
    Task8LiveMutationTarget,
    T,
    ScheduledReadback<T>,
)>
where
    T: Copy + Default + Send + Sync + 'static,
{
    let staging = alloc_static_pinned_box_from_slice(&[value])?;
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(destination, 1) };
    memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    let readback = schedule_read_device_chunked(destination, readback_scratch, callbacks, context)?;
    retain_in_callback(staging, callbacks, context)?;
    Ok((family, target, value, readback))
}

fn build_prior_level(
    storage: &GpuGKRStorage<BF, E4>,
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    target_start: usize,
    claim_point: *const E4,
    eq_low: &mut DeviceAllocation<E4>,
    partials: &mut DeviceAllocation<E4>,
    context: &ProverContext,
) -> CudaResult<Option<ContinuationPublishedLevel>> {
    let mut prior = None;
    for pass_start in (3..target_start).step_by(3) {
        launch_build_eq_high_and_low_groups_from_point(
            claim_point,
            pass_start + 3,
            folding_steps - pass_start - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        launch_bwd_seg_build_fold_weights(pass_start as u32, context)?;
        let scratch = MainContinuationWindowRuntimeScratch {
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        };
        let launch = match prior.as_ref() {
            None => bind_first_main_continuation_window(
                program,
                storage,
                folding_steps,
                pass_start,
                scratch,
                context,
            ),
            Some(prior) => bind_later_main_continuation_window(
                program,
                prior,
                folding_steps,
                pass_start,
                scratch,
                context,
            ),
        }
        .unwrap_or_else(|error| panic!("Task 8 prior pass {pass_start}: {error:?}"));
        let launched = launch_main_continuation_window(launch, context)?;
        let consumed = prior.take();
        prior = Some(launched.into_published_level());
        drop(consumed);
    }
    Ok(prior)
}

#[allow(clippy::too_many_arguments)]
fn run_window_arm(
    storage: &GpuGKRStorage<BF, E4>,
    window_program: &MainContinuationWindowProgram,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    start_round: usize,
    point_host: &[E4],
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledPreparedObservation> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (mut observation, allocations) = {
        let mut allocations = Vec::new();
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
        let before_eq = context.get_device_memory_usage();
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let after_eq = context.get_device_memory_usage();
        let before_partials = after_eq;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let after_partials = context.get_device_memory_usage();
        allocations.push(allocation_record_with_usage(
            "eq", &eq_low, 1, 8, 1, "best_fit", before_eq, after_eq,
        ));
        allocations.push(allocation_record_with_usage(
            "partials",
            &partials,
            1,
            8,
            1,
            "best_fit",
            before_partials,
            after_partials,
        ));
        let bank_observer = context.observe_device_memory_high_water();
        let mut bank =
            prepare_continuation_differential_bank(continuation_program, top_bits, context)?;
        let bank_report = bank_observer.finish();
        allocations.push(allocation_group_record(
            "bank",
            bank.challenge_slab().as_ptr() as usize,
            1,
            8,
            1,
            "mixed",
            2,
            &bank_report,
        ));
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        bank.schedule(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;

        let before_prior = context.get_device_memory_usage();
        let prior_observer = context.observe_device_memory_high_water();
        let prior = build_prior_level(
            storage,
            window_program,
            folding_steps,
            start_round,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
        )?;
        let after_prior = context.get_device_memory_usage();
        let prior_report = prior_observer.finish();
        if let Some(prior) = prior.as_ref() {
            let mut record = allocation_record_with_usage(
                "prior_publication",
                prior.allocation(),
                2,
                3,
                1,
                "best_fit",
                before_prior,
                after_prior,
            );
            record.successful_requested_bytes = prior_report.summed_requested_bytes;
            record.multiplicity = start_round / 3 - 1;
            allocations.push(record);
        }
        let prior_original = prior
            .as_ref()
            .map(|prior| {
                let first = unsafe { DeviceSlice::from_raw_parts(prior.allocation().as_ptr(), 1) };
                schedule_read_device_chunked(first, readback_scratch, callbacks, context)
            })
            .transpose()?;
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        launch_bwd_seg_build_fold_weights(start_round as u32, context)?;
        let scratch = MainContinuationWindowRuntimeScratch {
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        };
        let before_binding = context.get_device_memory_usage();
        let binding_observer = context.observe_device_memory_high_water();
        let launch = match prior.as_ref() {
            None => bind_first_main_continuation_window(
                window_program,
                storage,
                folding_steps,
                start_round,
                scratch,
                context,
            ),
            Some(prior) => bind_later_main_continuation_window(
                window_program,
                prior,
                folding_steps,
                start_round,
                scratch,
                context,
            ),
        }
        .unwrap_or_else(|error| panic!("Task 8 window pass {start_round}: {error:?}"));
        allocations.push(Task8AllocationRecord {
            kind: "descriptor",
            owner: (&launch as *const _) as usize,
            size_bytes: std::mem::size_of_val(&launch),
            successful_requested_bytes: std::mem::size_of_val(&launch),
            physical_backing_delta_bytes: 0,
            logical_live_delta_bytes: 0,
            multiplicity: 1,
            live_from: 3,
            live_until: 4,
            overlap_group: 2,
            placement: "host_box",
            retired: true,
        });
        let launched = launch_main_continuation_window(launch, context)?;
        let after_binding = context.get_device_memory_usage();
        let binding_report = binding_observer.finish();
        let mut publication_record = allocation_record_with_usage(
            "publication",
            launched.published_level().allocation(),
            3,
            8,
            2,
            "best_fit",
            before_binding,
            after_binding,
        );
        publication_record.successful_requested_bytes = binding_report.summed_requested_bytes;
        allocations.push(publication_record);
        let pre_sizes = launched.eq_sizes();
        let pre_eq =
            schedule_read_all_eq(pre_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let mut transcript = transcript_buffers(context)?;
        allocations.append(&mut transcript.allocations);
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot(&pre_sizes, eq_low.as_mut_ptr());
        let tail = WindowTailState {
            partials: partials.as_ptr(),
            row_tiles: launched.row_tiles(),
            reduced_tensor: launched.reduced_tensor(),
            prev_claim_coords: unsafe { claim_point.as_ptr().add(start_round) },
            seed: transcript.seed.as_mut_ptr(),
            claim: transcript.claim.as_mut_ptr(),
            eq_prefactor: transcript.prefactor.as_mut_ptr(),
            coeffs_out: transcript.coefficients.as_mut_ptr(),
            challenges_out: transcript.challenges.as_mut_ptr(),
            active_eq_slot_base,
            active_eq_size_before_fold,
        };
        launch_window_tensor_round_tail(WindowTailArm::Split, &tail, context)?;
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let publication = schedule_read_device_chunked(
            launched.published_level().allocation(),
            readback_scratch,
            callbacks,
            context,
        )?;
        let coefficients = schedule_read_device_chunked(
            &transcript.coefficients,
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_read_device_chunked(
            &transcript.challenges,
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed =
            schedule_read_device_chunked(&transcript.seed, readback_scratch, callbacks, context)?;
        let claim =
            schedule_read_device_chunked(&transcript.claim, readback_scratch, callbacks, context)?;
        let eq_prefactor = schedule_read_device_chunked(
            &transcript.prefactor,
            readback_scratch,
            callbacks,
            context,
        )?;
        let post_eq =
            schedule_read_all_eq(post_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let boundary =
            main_continuation_post_tail_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let mut live_mutations = ScheduledLiveMutationEvidence::empty();
        live_mutations.prior_original = prior_original;
        live_mutations.e4.push(schedule_live_device_mutation(
            "window-publication-lane",
            Task8LiveMutationTarget::Publication(0),
            launched.published_level().allocation().as_ptr() as *mut E4,
            deterministic_e4(0x981),
            readback_scratch,
            callbacks,
            context,
        )?);
        for (index, tag) in [(0usize, 0x982), (4, 0x983), (8, 0x984)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "axis-product-infinity-coefficients",
                Task8LiveMutationTarget::Coefficient(index),
                unsafe { transcript.coefficients.as_mut_ptr().add(index) },
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        live_mutations.e4.push(schedule_live_device_mutation(
            "row-weight",
            Task8LiveMutationTarget::Coefficient(1),
            unsafe { transcript.coefficients.as_mut_ptr().add(1) },
            deterministic_e4(0x985),
            readback_scratch,
            callbacks,
            context,
        )?);
        for (index, tag) in [(0usize, 0x986), (1, 0x987), (2, 0x988)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "challenges",
                Task8LiveMutationTarget::Challenge(index),
                unsafe { transcript.challenges.as_mut_ptr().add(index) },
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        live_mutations.u32.push(schedule_live_device_mutation(
            "transcript-seed",
            Task8LiveMutationTarget::Seed(0),
            transcript.seed.as_mut_ptr(),
            0xa5a5_5a5a,
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "claim",
            Task8LiveMutationTarget::Claim(0),
            transcript.claim.as_mut_ptr(),
            deterministic_e4(0x989),
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "eq-prefactor",
            Task8LiveMutationTarget::EqPrefactor(0),
            transcript.prefactor.as_mut_ptr(),
            deterministic_e4(0x98a),
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "stale-eq",
            Task8LiveMutationTarget::PostEqLow(0),
            eq_low.as_mut_ptr(),
            deterministic_e4(0x98b),
            readback_scratch,
            callbacks,
            context,
        )?);
        if let Some(prior) = prior.as_ref() {
            live_mutations.e4.push(schedule_live_device_mutation(
                "prior-publication-cell",
                Task8LiveMutationTarget::PriorPublication,
                prior.allocation().as_ptr() as *mut E4,
                deterministic_e4(0x98c),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        drop(prior);
        if let Some(bank_staging) = bank.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        retain_in_callback(transcript._seed_staging, callbacks, context)?;
        retain_in_callback(transcript._claim_staging, callbacks, context)?;
        retain_in_callback(transcript._prefactor_staging, callbacks, context)?;
        drop(launched);
        drop(bank);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        drop(transcript.challenges);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        let memory = observer.finish();
        (
            ScheduledPreparedObservation {
                publication,
                coefficients,
                challenges,
                seed,
                claim,
                eq_prefactor,
                pre_eq,
                post_eq,
                boundary: (
                    boundary.consumer_round,
                    boundary.semantic_suffix_offset,
                    boundary.eq_sizes,
                ),
                memory,
                allocations: Vec::new(),
                live_mutations,
            },
            allocations,
        )
    };
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    observation.allocations = allocations;
    Ok(observation)
}

#[allow(clippy::too_many_arguments)]
fn run_legacy_arm(
    storage: &GpuGKRStorage<BF, E4>,
    window_program: &MainContinuationWindowProgram,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    start_round: usize,
    point_host: &[E4],
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<(
    ScheduledPreparedObservation,
    Vec<(SourceId, usize)>,
    ContinuationPublishedShape,
    Task8AdoptionEvidence,
)> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (mut observation, source_columns, shape, adoption, allocations) = {
        let mut allocations = Vec::new();
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
        let before_eq = context.get_device_memory_usage();
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let after_eq = context.get_device_memory_usage();
        let before_partials = after_eq;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let after_partials = context.get_device_memory_usage();
        allocations.push(allocation_record_with_usage(
            "eq", &eq_low, 1, 8, 1, "best_fit", before_eq, after_eq,
        ));
        allocations.push(allocation_record_with_usage(
            "partials",
            &partials,
            1,
            8,
            1,
            "best_fit",
            before_partials,
            after_partials,
        ));
        let before_prior = context.get_device_memory_usage();
        let prior_observer = context.observe_device_memory_high_water();
        let prior = build_prior_level(
            storage,
            window_program,
            folding_steps,
            start_round,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
        )?;
        let after_prior = context.get_device_memory_usage();
        let prior_report = prior_observer.finish();
        if let Some(prior) = prior.as_ref() {
            let mut record = allocation_record_with_usage(
                "prior_publication",
                prior.allocation(),
                2,
                3,
                1,
                "best_fit",
                before_prior,
                after_prior,
            );
            record.successful_requested_bytes = prior_report.summed_requested_bytes;
            record.multiplicity = start_round / 3 - 1;
            allocations.push(record);
        }
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        let pre_sizes = make_eq_sizes(folding_steps - start_round - 3);
        let pre_eq =
            schedule_read_all_eq(pre_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let bank_observer = context.observe_device_memory_high_water();
        let mut rounds = prepare_continuation_differential_rounds(
            storage,
            continuation_program,
            start_round as u8,
            folding_steps,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
            prior,
            top_bits,
            context,
        )?;
        let bank_report = bank_observer.finish();
        allocations.push(allocation_group_record(
            "bank",
            rounds.challenge_slab().as_ptr() as usize,
            2,
            8,
            1,
            "mixed",
            2,
            &bank_report,
        ));
        let input_live_before = rounds.expected_input_is_live();
        let first_deltas = rounds.first_deltas().to_vec();
        let first_reads_only_published = rounds.first_reads_only_published();
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        rounds.schedule_bank_fill(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        let mut transcript = transcript_buffers(context)?;
        allocations.append(&mut transcript.allocations);
        let mut raw_publication = None;
        for local_round in 0..3 {
            let round = start_round + local_round;
            let acc_size = 1usize << (folding_steps - round - 1);
            let before_round = context.get_device_memory_usage();
            rounds.schedule_round(round as u32, acc_size as u32, context)?;
            let after_round = context.get_device_memory_usage();
            if local_round == 0 {
                allocations.push(allocation_record_with_usage(
                    "publication",
                    rounds.live_publication(),
                    3,
                    5,
                    2,
                    "top",
                    before_round,
                    after_round,
                ));
                raw_publication = Some(schedule_read_device_chunked(
                    rounds.live_publication(),
                    readback_scratch,
                    callbacks,
                    context,
                )?);
            }
            let (active_eq_slot_base, active_eq_size_before_fold) = if local_round == 2 {
                resolve_active_eq_slot(&pre_sizes, eq_low.as_mut_ptr())
            } else {
                (eq_low.as_mut_ptr(), 0)
            };
            launch_backward_dual_finalize_from_partials(
                partials.as_ptr(),
                warp_partial_count(acc_size),
                unsafe { claim_point.as_ptr().add(round) },
                transcript.seed.as_mut_ptr(),
                transcript.claim.as_mut_ptr(),
                transcript.prefactor.as_mut_ptr(),
                unsafe { transcript.coefficients.as_mut_ptr().add(4 * local_round) },
                unsafe { transcript.challenges.as_mut_ptr().add(local_round) },
                active_eq_slot_base,
                active_eq_size_before_fold,
                context,
            )?;
        }
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let source_columns = rounds.source_columns().to_vec();
        let shape = rounds.publication_shape();
        assert_eq!(shape.depth, start_round as u8);
        let publication = raw_publication.expect("Task 8 legacy round did not publish");
        let coefficients = schedule_read_device_chunked(
            &transcript.coefficients,
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_read_device_chunked(
            &transcript.challenges,
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed =
            schedule_read_device_chunked(&transcript.seed, readback_scratch, callbacks, context)?;
        let claim =
            schedule_read_device_chunked(&transcript.claim, readback_scratch, callbacks, context)?;
        let eq_prefactor = schedule_read_device_chunked(
            &transcript.prefactor,
            readback_scratch,
            callbacks,
            context,
        )?;
        let post_eq =
            schedule_read_all_eq(post_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let boundary =
            main_continuation_post_tail_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let adoption = Task8AdoptionEvidence {
            had_prior: start_round > 3,
            input_live_before,
            first_deltas,
            first_reads_only_published,
            input_retired: !rounds.expected_input_is_live(),
        };
        if let Some(bank_staging) = rounds.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        retain_in_callback(transcript._seed_staging, callbacks, context)?;
        retain_in_callback(transcript._claim_staging, callbacks, context)?;
        retain_in_callback(transcript._prefactor_staging, callbacks, context)?;
        drop(rounds);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        drop(transcript.challenges);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        let memory = observer.finish();
        (
            ScheduledPreparedObservation {
                publication,
                coefficients,
                challenges,
                seed,
                claim,
                eq_prefactor,
                pre_eq,
                post_eq,
                boundary: (
                    boundary.consumer_round,
                    boundary.semantic_suffix_offset,
                    boundary.eq_sizes,
                ),
                memory,
                allocations: Vec::new(),
                live_mutations: ScheduledLiveMutationEvidence::empty(),
            },
            source_columns,
            shape,
            adoption,
            allocations,
        )
    };
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    observation.allocations = allocations;
    Ok((observation, source_columns, shape, adoption))
}

struct Task8CapacityEvidence {
    publication_bytes: usize,
    overlap_event: Task8LivePublicationEvent,
    memory: PoolMemoryHighWaterReport,
}

#[allow(clippy::too_many_arguments)]
fn run_first_pass_legacy_capacity_probe(
    storage: &GpuGKRStorage<BF, E4>,
    window_program: &MainContinuationWindowProgram,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    point_host: &[E4],
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<Task8CapacityEvidence> {
    let entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (publication_bytes, overlap_event) = {
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let prior = build_prior_level(
            storage,
            window_program,
            folding_steps,
            3,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
        )?;
        assert!(
            prior.is_none(),
            "round-3 capacity probe must not retain a prior"
        );
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            6,
            folding_steps - 6,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        let mut rounds = prepare_continuation_differential_rounds(
            storage,
            continuation_program,
            3,
            folding_steps,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
            None,
            top_bits,
            context,
        )?;
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        rounds.schedule_bank_fill(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        let mut publication_bytes = 0usize;
        for local_round in 0..3 {
            let round = 3 + local_round;
            let acc_size = 1usize << (folding_steps - round - 1);
            rounds.schedule_round(round as u32, acc_size as u32, context)?;
            if local_round == 0 {
                publication_bytes = rounds
                    .live_publication()
                    .len()
                    .checked_mul(std::mem::size_of::<E4>())
                    .expect("Task 8 capacity publication bytes overflowed usize");
            }
        }
        let overlap_event = rounds
            .live_publication_events()
            .iter()
            .find(|event| event.round == 4)
            .cloned()
            .expect("Task 8 capacity probe did not retain the round-4 overlap event");
        assert_eq!(overlap_event.owners.len(), 2);
        assert_eq!(overlap_event.owners[0].0, 3);
        assert_eq!(overlap_event.owners[0].2, publication_bytes);
        assert_eq!(overlap_event.owners[1].0, 4);
        assert_eq!(overlap_event.owners[1].2, publication_bytes / 2);
        assert_ne!(overlap_event.owners[0].1, overlap_event.owners[1].1);
        assert_eq!(
            rounds.peak_live_publications(),
            (2, publication_bytes + publication_bytes / 2)
        );
        if let Some(bank_staging) = rounds.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        drop(rounds);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        (publication_bytes, overlap_event)
    };
    let memory = observer.finish();
    assert_eq!(memory.start, entry);
    assert_eq!(memory.return_to_entry, entry);
    if publication_bytes > 2usize << 30 {
        assert!(memory.physical_backing_peak_bytes > 2usize << 30);
        assert!(memory.logical_live_peak_bytes > 2usize << 30);
    }
    Ok(Task8CapacityEvidence {
        publication_bytes,
        overlap_event,
        memory,
    })
}

fn schedule_source_identity(
    storage: &GpuGKRStorage<BF, E4>,
    program: &MainContinuationWindowProgram,
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<Vec<ScheduledSourceIdentityRecord>> {
    let mut semantic_ids = BTreeSet::new();
    let mut physical_views = std::collections::BTreeMap::new();
    let mut records = Vec::new();
    for source in &program.sources {
        assert!(semantic_ids.insert(source.id.0));
        if let Some(place) = family_read_place(source.raw_family, source.raw_column) {
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_storage_column(storage, address).unwrap_or_else(|| {
                panic!(
                    "Task 8 source {} address {address:?} is absent",
                    source.id.0
                )
            });
            let pointer = resolved.ptr as usize;
            let base = resolved.matrix_base as usize;
            assert!(pointer >= base);
            assert_eq!((pointer - base) % resolved.stride_bytes as usize, 0);
            let view = (resolved.is_e4, base, pointer - base, resolved.stride_bytes);
            if let Some(previous_address) = physical_views.insert(view, address) {
                if previous_address != address {
                    let aliases = storage
                        .layout
                        .as_ref()
                        .map(|layout| &layout.aliases)
                        .expect("shared Task 8 backing views require an artifact layout");
                    let canonical =
                        |candidate| aliases.get(&candidate).copied().unwrap_or(candidate);
                    assert_eq!(
                        canonical(previous_address),
                        canonical(address),
                        "Task 8 source {} shares an unexplained physical view",
                        source.id.0
                    );
                }
            }
            let elements = resolved.stride_bytes as usize
                / if resolved.is_e4 {
                    std::mem::size_of::<E4>()
                } else {
                    std::mem::size_of::<BF>()
                };
            assert!(elements > 0);
            let sample_indices = if elements == 1 {
                vec![0]
            } else {
                vec![0, elements - 1]
            };
            let samples = if resolved.is_e4 {
                ScheduledSourceSampleValues::Extension(
                    sample_indices
                        .into_iter()
                        .map(|index| {
                            let sample = unsafe {
                                DeviceSlice::from_raw_parts(
                                    (resolved.ptr as *const E4).add(index),
                                    1,
                                )
                            };
                            schedule_read_device_chunked(
                                sample,
                                readback_scratch,
                                callbacks,
                                context,
                            )
                        })
                        .collect::<CudaResult<Vec<_>>>()?,
                )
            } else {
                ScheduledSourceSampleValues::Base(
                    sample_indices
                        .into_iter()
                        .map(|index| {
                            let sample = unsafe {
                                DeviceSlice::from_raw_parts(
                                    (resolved.ptr as *const BF).add(index),
                                    1,
                                )
                            };
                            schedule_read_device_chunked(
                                sample,
                                readback_scratch,
                                callbacks,
                                context,
                            )
                        })
                        .collect::<CudaResult<Vec<_>>>()?,
                )
            };
            let backing_bytes = if resolved.is_e4 {
                storage
                    .get_ext_poly_for_address(address)
                    .expect("Task 8 extension source lost its storage owner")
                    .backing
                    .len()
                    .checked_mul(std::mem::size_of::<E4>())
                    .expect("Task 8 extension backing byte count overflowed usize")
            } else {
                storage
                    .get_base_poly_for_address(address)
                    .expect("Task 8 base source lost its storage owner")
                    .backing
                    .len()
                    .checked_mul(std::mem::size_of::<BF>())
                    .expect("Task 8 base backing byte count overflowed usize")
            };
            records.push(ScheduledSourceIdentityRecord {
                source: source.id,
                address,
                field_class: if resolved.is_e4 {
                    Task8SourceFieldClass::Extension
                } else {
                    Task8SourceFieldClass::Base
                },
                backing_base: base,
                view_offset: pointer - base,
                stride_bytes: resolved.stride_bytes as usize,
                backing_bytes,
                backing_requested_bytes: backing_bytes,
                samples,
            });
        }
    }
    assert_eq!(semantic_ids.len(), program.sources.len());
    Ok(records)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationMismatch {
    Publication,
    Coefficients,
    Challenges,
    Seed,
    Claim,
    EqPrefactor,
    PreEqSizes,
    PreEqLow,
    PreEqHigh,
    PostEqSizes,
    PostEqLow,
    PostEqHigh,
    Boundary,
}

fn compare_observations(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
) -> Result<usize, ObservationMismatch> {
    if window.publication != legacy.publication {
        return Err(ObservationMismatch::Publication);
    }
    if window.coefficients != legacy.coefficients {
        return Err(ObservationMismatch::Coefficients);
    }
    if window.challenges != legacy.challenges {
        return Err(ObservationMismatch::Challenges);
    }
    if window.seed != legacy.seed {
        return Err(ObservationMismatch::Seed);
    }
    if window.claim != legacy.claim {
        return Err(ObservationMismatch::Claim);
    }
    if window.eq_prefactor != legacy.eq_prefactor {
        return Err(ObservationMismatch::EqPrefactor);
    }
    if window.pre_eq.sizes != legacy.pre_eq.sizes {
        return Err(ObservationMismatch::PreEqSizes);
    }
    if window.pre_eq.low != legacy.pre_eq.low {
        return Err(ObservationMismatch::PreEqLow);
    }
    if window.pre_eq.high != legacy.pre_eq.high {
        return Err(ObservationMismatch::PreEqHigh);
    }
    if window.post_eq.sizes != legacy.post_eq.sizes {
        return Err(ObservationMismatch::PostEqSizes);
    }
    if window.post_eq.low != legacy.post_eq.low {
        return Err(ObservationMismatch::PostEqLow);
    }
    if window.post_eq.high != legacy.post_eq.high {
        return Err(ObservationMismatch::PostEqHigh);
    }
    if window.boundary != legacy.boundary {
        return Err(ObservationMismatch::Boundary);
    }
    Ok(window.publication.len()
        + window.coefficients.len()
        + window.challenges.len()
        + window.seed.len()
        + window.claim.len()
        + window.eq_prefactor.len()
        + window.pre_eq.low.len()
        + window.pre_eq.high.len()
        + window.post_eq.low.len()
        + window.post_eq.high.len()
        + 3)
}

fn run_comparator_field_coverage_checks(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
) -> usize {
    let mutations: Vec<(ObservationMismatch, Box<dyn Fn(&mut PreparedObservation)>)> = vec![
        (
            ObservationMismatch::Publication,
            Box::new(|value| value.publication[0] = deterministic_e4(0x901)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[0] = deterministic_e4(0x902)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[4] = deterministic_e4(0x912)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[8] = deterministic_e4(0x922)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[0] = deterministic_e4(0x903)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[1] = deterministic_e4(0x913)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[2] = deterministic_e4(0x923)),
        ),
        (
            ObservationMismatch::Seed,
            Box::new(|value| value.seed[0] ^= 1),
        ),
        (
            ObservationMismatch::Claim,
            Box::new(|value| value.claim[0] = deterministic_e4(0x904)),
        ),
        (
            ObservationMismatch::EqPrefactor,
            Box::new(|value| value.eq_prefactor[0] = deterministic_e4(0x905)),
        ),
        (
            ObservationMismatch::PreEqSizes,
            Box::new(|value| value.pre_eq.sizes.low ^= 1),
        ),
        (
            ObservationMismatch::PreEqLow,
            Box::new(|value| value.pre_eq.low[0] = deterministic_e4(0x906)),
        ),
        (
            ObservationMismatch::PreEqHigh,
            Box::new(|value| value.pre_eq.high[0] = deterministic_e4(0x916)),
        ),
        (
            ObservationMismatch::PostEqSizes,
            Box::new(|value| value.post_eq.sizes.low ^= 1),
        ),
        (
            ObservationMismatch::PostEqLow,
            Box::new(|value| value.post_eq.low[0] = deterministic_e4(0x917)),
        ),
        (
            ObservationMismatch::PostEqHigh,
            Box::new(|value| value.post_eq.high[0] = deterministic_e4(0x907)),
        ),
        (
            ObservationMismatch::Boundary,
            Box::new(|value| value.boundary.0 ^= 1),
        ),
    ];
    for (expected, mutate) in &mutations {
        let mut changed = window.clone();
        mutate(&mut changed);
        assert_eq!(
            compare_observations(&changed, legacy),
            Err(*expected),
            "Task 8 mutation did not reach its live semantic oracle"
        );
    }
    mutations.len()
}

fn validate_live_observation_mutations(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
    mutations: ScheduledLiveMutationEvidence,
) -> (usize, BTreeSet<String>) {
    let mut checks = 0usize;
    let mut families = BTreeSet::new();
    for mutation in mutations.materialize() {
        let (family, target, e4_value, u32_value) = match mutation {
            Task8MaterializedLiveMutation::E4(family, target, value) => {
                (family, target, Some(value), None)
            }
            Task8MaterializedLiveMutation::U32(family, target, value) => {
                (family, target, None, Some(value))
            }
        };
        if matches!(target, Task8LiveMutationTarget::PriorPublication) {
            assert!(e4_value.is_some());
            families.insert(family.to_owned());
            checks += 1;
            continue;
        }
        let mut changed = window.clone();
        let expected = match target {
            Task8LiveMutationTarget::Publication(index) => {
                changed.publication[index] = e4_value.expect("E4 publication mutation");
                ObservationMismatch::Publication
            }
            Task8LiveMutationTarget::Coefficient(index) => {
                changed.coefficients[index] = e4_value.expect("E4 coefficient mutation");
                ObservationMismatch::Coefficients
            }
            Task8LiveMutationTarget::Challenge(index) => {
                changed.challenges[index] = e4_value.expect("E4 challenge mutation");
                ObservationMismatch::Challenges
            }
            Task8LiveMutationTarget::Seed(index) => {
                changed.seed[index] = u32_value.expect("u32 seed mutation");
                ObservationMismatch::Seed
            }
            Task8LiveMutationTarget::Claim(index) => {
                changed.claim[index] = e4_value.expect("E4 claim mutation");
                ObservationMismatch::Claim
            }
            Task8LiveMutationTarget::EqPrefactor(index) => {
                changed.eq_prefactor[index] = e4_value.expect("E4 Eq-prefactor mutation");
                ObservationMismatch::EqPrefactor
            }
            Task8LiveMutationTarget::PostEqLow(index) => {
                changed.post_eq.low[index] = e4_value.expect("E4 post-Eq mutation");
                ObservationMismatch::PostEqLow
            }
            Task8LiveMutationTarget::PriorPublication => unreachable!(),
        };
        assert_eq!(
            compare_observations(&changed, legacy),
            Err(expected),
            "Task 8 live {family} mutation did not reach its semantic oracle"
        );
        families.insert(family.to_owned());
        checks += 1;
    }

    let mut boundary = window.clone();
    boundary.boundary.0 ^= 1;
    assert_eq!(
        compare_observations(&boundary, legacy),
        Err(ObservationMismatch::Boundary)
    );
    assert!(families.insert("final-boundary-repoint".to_owned()));
    checks += 1;
    (checks, families)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8TopologyError {
    ProductionStorageCount,
    InvalidLifetime,
    UnretiredOwner,
    MissingAllocationEvidence,
    DuplicateRawBacking,
    OverlappingPrior,
    OverlappingOwner,
}

fn validate_single_owner_topology(
    records: &[Task8AllocationRecord],
) -> Result<(), Task8TopologyError> {
    let storage: Vec<_> = records
        .iter()
        .filter(|record| record.kind == "production_storage")
        .collect();
    if storage.len() != 1 {
        return Err(Task8TopologyError::ProductionStorageCount);
    }
    let storage = storage[0];
    for record in records {
        if record.live_from >= record.live_until
            || record.live_from < storage.live_from
            || record.live_until > storage.live_until
        {
            return Err(Task8TopologyError::InvalidLifetime);
        }
        if !record.retired && record.kind != "production_storage" {
            return Err(Task8TopologyError::UnretiredOwner);
        }
        if record.kind != "production_storage"
            && (record.size_bytes == 0 || record.successful_requested_bytes == 0)
        {
            return Err(Task8TopologyError::MissingAllocationEvidence);
        }
    }
    for (index, left) in records.iter().enumerate() {
        for right in &records[index + 1..] {
            let overlap = left.live_from < right.live_until && right.live_from < left.live_until;
            if !overlap || left.owner != right.owner {
                continue;
            }
            if left.kind == "raw_backing" && right.kind == "raw_backing" {
                return Err(Task8TopologyError::DuplicateRawBacking);
            }
            if left.kind == "prior_publication" && right.kind == "prior_publication" {
                return Err(Task8TopologyError::OverlappingPrior);
            }
            if left.kind != "production_storage" && right.kind != "production_storage" {
                return Err(Task8TopologyError::OverlappingOwner);
            }
        }
    }
    let priors: Vec<_> = records
        .iter()
        .filter(|record| record.kind == "prior_publication")
        .collect();
    for (index, left) in priors.iter().enumerate() {
        for right in &priors[index + 1..] {
            if left.live_from < right.live_until && right.live_from < left.live_until {
                return Err(Task8TopologyError::OverlappingPrior);
            }
        }
    }
    Ok(())
}

fn actual_topology_records(
    storage_owner: usize,
    sources: &[Task8SourceIdentityRecord],
    arm_records: &[Task8AllocationRecord],
) -> Vec<Task8AllocationRecord> {
    let mut records = vec![Task8AllocationRecord {
        kind: "production_storage",
        owner: storage_owner,
        size_bytes: 0,
        successful_requested_bytes: 0,
        physical_backing_delta_bytes: 0,
        logical_live_delta_bytes: 0,
        multiplicity: 1,
        live_from: 0,
        live_until: 100,
        overlap_group: 0,
        placement: "top",
        retired: true,
    }];
    let mut raw_backings = std::collections::BTreeMap::new();
    for source in sources {
        let evidence = (source.backing_bytes, source.backing_requested_bytes);
        if let Some(previous) = raw_backings.insert(source.backing_base, evidence) {
            assert_eq!(
                previous, evidence,
                "Task 8 consolidated raw backing has inconsistent size evidence"
            );
        }
    }
    records.extend(
        raw_backings
            .into_iter()
            .map(
                |(owner, (size_bytes, requested_bytes))| Task8AllocationRecord {
                    kind: "raw_backing",
                    owner,
                    size_bytes,
                    successful_requested_bytes: requested_bytes,
                    physical_backing_delta_bytes: size_bytes as i128,
                    logical_live_delta_bytes: requested_bytes as i128,
                    multiplicity: 1,
                    live_from: 0,
                    live_until: 100,
                    overlap_group: 0,
                    placement: "top",
                    retired: true,
                },
            ),
    );
    records.extend_from_slice(arm_records);
    records
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CorpusCensus {
    layouts: usize,
    layers: usize,
    coordinates: usize,
    folding_steps: Vec<usize>,
    start_rounds: Vec<usize>,
    masks: Vec<u16>,
    max_sources: usize,
    max_legacy_displacement: usize,
    publication_over_2gib: usize,
}

fn build_corpus_census() -> CorpusCensus {
    use std::collections::BTreeSet;

    use crate::backward::compile_corpus_layout;
    use crate::main_layer_execution_plan::{
        try_derive_main_layer_execution_plan, MainTailRoundBudget, LEGACY_MAIN_TAIL_MIN_ROUNDS,
    };
    use crate::{BackwardExecutionStrategy, GkrBackwardOptions};

    let mut folding_steps_seen = BTreeSet::new();
    let mut start_rounds_seen = BTreeSet::new();
    let mut masks_seen = BTreeSet::new();
    let mut layers = 0usize;
    let mut max_sources = 0usize;
    let mut max_legacy_displacement = 0usize;
    let mut publication_over_2gib = 0usize;

    for (layout, _) in crate::backward::CONTINUATION_GOLDEN_CORPUS {
        let (programs, layout_layers) = compile_corpus_layout(layout);
        let bundle = programs
            .resolve_main_continuation_window_programs()
            .expect("the retained Task 8 corpus must lower");
        let folding_steps = programs.runtime_circuit().trace_len.trailing_zeros() as usize;
        folding_steps_seen.insert(folding_steps);
        let plan = try_derive_main_layer_execution_plan(
            GkrBackwardOptions {
                windowed_r0: true,
                windowed_main_continuations: true,
                ..GkrBackwardOptions::default()
            },
            BackwardExecutionStrategy::WindowedR0,
            folding_steps,
            MainTailRoundBudget::AtLeast {
                min_tail_rounds: LEGACY_MAIN_TAIL_MIN_ROUNDS,
            },
        )
        .expect("the retained Task 8 corpus must have a continuation plan");
        let starts: Vec<_> = (0..usize::from(plan.window_count()))
            .map(|index| 3 * (index + 1))
            .collect();
        start_rounds_seen.extend(starts.iter().copied());

        assert_eq!(bundle.layers.len(), layout_layers, "{layout}");
        for (layer, program) in bundle.layers.iter().enumerate() {
            layers += 1;
            masks_seen.insert(program.shape.bits());
            max_sources = max_sources.max(program.sources.len());
            let publication_bytes = program
                .sources
                .len()
                .checked_mul(1usize << (folding_steps - 3))
                .and_then(|elements| elements.checked_mul(std::mem::size_of::<E4>()))
                .expect("Task 8 publication bytes must fit usize");
            publication_over_2gib += usize::from(publication_bytes > 2usize << 30);

            let source_program = programs.continuation_layer(layer);
            let mut seen = vec![false; source_program.coefficients.sources.len()];
            let mut displaced = 0usize;
            for (published, column) in source_program
                .binding
                .windows
                .iter()
                .flat_map(|window| &window.columns)
                .enumerate()
            {
                let source = column.source as usize;
                assert!(source < seen.len(), "{layout} layer {layer}");
                assert!(!seen[source], "{layout} layer {layer} source {source}");
                seen[source] = true;
                displaced += usize::from(published != source);
            }
            assert!(seen.into_iter().all(|seen| seen), "{layout} layer {layer}");
            max_legacy_displacement = max_legacy_displacement.max(displaced);
        }
    }

    CorpusCensus {
        layouts: crate::backward::CONTINUATION_GOLDEN_CORPUS.len(),
        layers,
        coordinates: layers,
        folding_steps: folding_steps_seen.into_iter().collect(),
        start_rounds: start_rounds_seen.into_iter().collect(),
        masks: masks_seen.into_iter().collect(),
        max_sources,
        max_legacy_displacement,
        publication_over_2gib,
    }
}

#[cfg(test)]
mod cpu_tests {
    use gpu_prover_context::{PoolMemoryHighWaterReport, PoolMemoryUsage};

    use super::{
        allocation_group_record, build_corpus_census, signed_snapshot_delta,
        validate_single_owner_topology, Task8AllocationRecord, Task8TopologyError,
    };

    fn record(
        kind: &'static str,
        owner: usize,
        live_from: usize,
        live_until: usize,
    ) -> Task8AllocationRecord {
        Task8AllocationRecord {
            kind,
            owner,
            size_bytes: usize::from(kind != "production_storage"),
            successful_requested_bytes: usize::from(kind != "production_storage"),
            physical_backing_delta_bytes: 1,
            logical_live_delta_bytes: 1,
            multiplicity: 1,
            live_from,
            live_until,
            overlap_group: 0,
            placement: "test",
            retired: true,
        }
    }

    fn valid_topology() -> Vec<Task8AllocationRecord> {
        vec![
            record("production_storage", 1, 0, 20),
            record("raw_backing", 2, 0, 20),
            record("prior_publication", 3, 1, 5),
            record("publication", 4, 2, 6),
            record("prior_publication", 5, 10, 14),
            record("publication", 6, 11, 15),
        ]
    }

    #[test]
    fn cpu_main_continuation_task8_topology_rejects_duplicate_owner() {
        validate_single_owner_topology(&valid_topology()).unwrap();

        let mut duplicate_prior = valid_topology();
        duplicate_prior.push(record("prior_publication", 7, 3, 4));
        assert_eq!(
            validate_single_owner_topology(&duplicate_prior),
            Err(Task8TopologyError::OverlappingPrior)
        );

        let mut duplicate_raw = valid_topology();
        duplicate_raw.push(record("raw_backing", 2, 0, 20));
        assert_eq!(
            validate_single_owner_topology(&duplicate_raw),
            Err(Task8TopologyError::DuplicateRawBacking)
        );
    }

    #[test]
    fn cpu_main_continuation_task8_corpus_census() {
        let census = build_corpus_census();
        assert_eq!(census.layouts, 12);
        assert_eq!(census.layers, 57);
        assert_eq!(census.coordinates, 57);
        assert_eq!(census.folding_steps, [20, 22, 23, 24]);
        assert_eq!(census.start_rounds, [3, 6, 9, 12, 15, 18]);
        assert_eq!(census.masks, [0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f]);
        assert_eq!(census.max_sources, 1_012);
        assert_eq!(census.max_legacy_displacement, 174);
        assert_eq!(census.publication_over_2gib, 4);
    }

    #[test]
    fn cpu_main_continuation_snapshot_decrease_is_signed_not_checked_sub() {
        assert_eq!(signed_snapshot_delta(7, 11), -4);
    }

    #[test]
    fn cpu_main_continuation_snapshot_growth_and_zero_are_preserved() {
        let raw_requested_bytes = 128usize;
        let growth_record = allocation_group_record(
            "growth",
            7,
            0,
            1,
            0,
            "test",
            1,
            &PoolMemoryHighWaterReport {
                start: PoolMemoryUsage {
                    physical_backing_bytes: 7,
                    logical_live_bytes: 11,
                },
                physical_backing_peak_bytes: 19,
                logical_live_peak_bytes: 25,
                summed_requested_bytes: raw_requested_bytes,
                peak_window_end: PoolMemoryUsage {
                    physical_backing_bytes: 31,
                    logical_live_bytes: 41,
                },
                return_to_entry: PoolMemoryUsage {
                    physical_backing_bytes: 19,
                    logical_live_bytes: 25,
                },
            },
        );
        assert_eq!(growth_record.physical_backing_delta_bytes, 12);
        assert_eq!(growth_record.logical_live_delta_bytes, 14);
        assert_eq!(growth_record.size_bytes, raw_requested_bytes);
        assert_eq!(
            growth_record.successful_requested_bytes,
            raw_requested_bytes
        );
        assert!(i128::try_from(growth_record.size_bytes).unwrap() >= 0);
        assert_eq!(signed_snapshot_delta(7, 7), 0);
    }
}

struct Task8DifferentialAccumulator {
    layers: usize,
    coordinates: usize,
    folding_steps: BTreeSet<usize>,
    start_rounds: BTreeSet<usize>,
    masks: BTreeSet<u16>,
    max_sources: usize,
    max_legacy_displacement: usize,
    semantic_comparisons: usize,
    publication_elements_compared: usize,
    comparator_field_coverage_checks: usize,
    mutation_checks: usize,
    source_table_identity_rows: usize,
    source_identity_records: usize,
    source_id_census: std::collections::BTreeMap<usize, Vec<u32>>,
    source_backing_census: std::collections::BTreeMap<usize, usize>,
    allocation_records: usize,
    topology_owner_records: usize,
    topology_owner_kinds: BTreeSet<String>,
    topology_coordinates: usize,
    later_start_shared_prior_coordinates: usize,
    multi_source_coordinates: usize,
    arm_memory_comparisons: usize,
    procedural_source_records: usize,
    mutation_families: BTreeSet<String>,
    capacity_overlap_rows: usize,
    capacity_heavy_layers: Vec<usize>,
    capacity_publication_bytes: Vec<usize>,
    capacity_overlap_live_bytes: Vec<usize>,
    capacity_overlap_owner_counts: Vec<usize>,
    capacity_physical_peak_bytes: Vec<usize>,
    capacity_logical_peak_bytes: Vec<usize>,
}

const TASK8_MUTATION_FAMILIES: [&str; 16] = [
    "axis-product-infinity-coefficients",
    "challenges",
    "claim",
    "duplicate-missing-canonical-map",
    "duplicate-raw-owner",
    "eq-prefactor",
    "final-boundary-repoint",
    "overlapping-prior-owner",
    "prior-publication-cell",
    "row-weight",
    "seeded-adoption-delta-3",
    "source-column-displacement",
    "stale-eq",
    "transcript-seed",
    "window-publication-lane",
    "zero-remainder-take",
];

fn assert_source_records_nonvacuous(records: &[Task8SourceIdentityRecord], expected: usize) {
    assert_eq!(records.len(), expected);
    let mut source_ids = BTreeSet::new();
    let mut nonzero = 0usize;
    for record in records {
        assert!(source_ids.insert(record.source.0));
        match &record.samples {
            Task8SourceSampleValues::Base(values) => {
                assert!(!values.is_empty());
                nonzero += usize::from(values.iter().any(|value| !value.is_zero()));
            }
            Task8SourceSampleValues::Extension(values) => {
                assert!(!values.is_empty());
                nonzero += usize::from(values.iter().any(|value| !value.is_zero()));
            }
        }
    }
    if !records.is_empty() {
        assert!(
            nonzero > 0,
            "Task 8 production source samples were all zero"
        );
        assert!(
            records.len() == 1
                || records.iter().enumerate().any(|(index, left)| {
                    records[index + 1..]
                        .iter()
                        .any(|right| left.source != right.source && left.samples != right.samples)
                }),
            "Task 8 retained no distinct sampled tuples across semantic SourceIds"
        );
    }
}

struct Task8TopologyEvidence {
    mutation_checks: usize,
    owner_records: usize,
    owner_kinds: BTreeSet<String>,
}

fn validate_actual_topology_mutations(
    storage_owner: usize,
    sources: &[Task8SourceIdentityRecord],
    arm_records: &[Task8AllocationRecord],
) -> Task8TopologyEvidence {
    let records = actual_topology_records(storage_owner, sources, arm_records);
    validate_single_owner_topology(&records).expect("Task 8 live allocation topology is invalid");
    let owner_records = records.len();
    let owner_kinds = records
        .iter()
        .map(|record| record.kind.to_owned())
        .collect();
    let raw = records
        .iter()
        .find(|record| record.kind == "raw_backing")
        .cloned()
        .expect("Task 8 live topology retained no raw backing");
    let mut duplicate_raw = records.clone();
    duplicate_raw.push(raw);
    assert_eq!(
        validate_single_owner_topology(&duplicate_raw),
        Err(Task8TopologyError::DuplicateRawBacking)
    );
    let mut checks = 1usize;
    if let Some(prior) = records
        .iter()
        .find(|record| record.kind == "prior_publication")
        .cloned()
    {
        let mut duplicate_prior = records;
        let mut second = prior;
        second.owner ^= 1usize << (usize::BITS - 2);
        duplicate_prior.push(second);
        assert_eq!(
            validate_single_owner_topology(&duplicate_prior),
            Err(Task8TopologyError::OverlappingPrior)
        );
        checks += 1;
    }
    Task8TopologyEvidence {
        mutation_checks: checks,
        owner_records,
        owner_kinds,
    }
}

#[inline(never)]
pub(crate) fn schedule_prepared_main_continuation_differential(
    request: Task8ContinuationDifferentialRequest,
    storage: &GpuGKRStorage<BF, E4>,
    programs: &GkrPrograms,
    inits_and_teardowns_top_bits: &[u32],
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    let folding_steps = programs.runtime_circuit().trace_len.trailing_zeros() as usize;
    let plan = crate::main_continuation_window_count(
        GkrBackwardOptions {
            windowed_r0: true,
            windowed_main_continuations: true,
            ..GkrBackwardOptions::default()
        },
        BackwardExecutionStrategy::WindowedR0,
        folding_steps,
    )
    .expect("Task 8 fixture must admit the continuation plan");
    assert!(
        plan > 0,
        "{TASK8_DIAGNOSTIC}: fixture selected zero continuation passes"
    );

    let point_host: Vec<_> = (0..=folding_steps)
        .map(|coordinate| deterministic_e4(0x300 + coordinate as u32))
        .collect();
    let layers = programs.runtime_circuit().layers.len();
    let accumulator = Arc::new(Mutex::new(Task8DifferentialAccumulator {
        layers,
        coordinates: layers,
        folding_steps: BTreeSet::from([folding_steps]),
        start_rounds: BTreeSet::new(),
        masks: BTreeSet::new(),
        max_sources: 0,
        max_legacy_displacement: 0,
        semantic_comparisons: 0,
        publication_elements_compared: 0,
        comparator_field_coverage_checks: 0,
        mutation_checks: 0,
        source_table_identity_rows: 0,
        source_identity_records: 0,
        source_id_census: std::collections::BTreeMap::new(),
        source_backing_census: std::collections::BTreeMap::new(),
        allocation_records: 0,
        topology_owner_records: 0,
        topology_owner_kinds: BTreeSet::new(),
        topology_coordinates: 0,
        later_start_shared_prior_coordinates: 0,
        multi_source_coordinates: 0,
        arm_memory_comparisons: 0,
        procedural_source_records: 0,
        mutation_families: BTreeSet::new(),
        capacity_overlap_rows: 0,
        capacity_heavy_layers: Vec::new(),
        capacity_publication_bytes: Vec::new(),
        capacity_overlap_live_bytes: Vec::new(),
        capacity_overlap_owner_counts: Vec::new(),
        capacity_physical_peak_bytes: Vec::new(),
        capacity_logical_peak_bytes: Vec::new(),
    }));
    let mut readback_scratch = alloc_static_pinned_box_uninit(TASK8_READBACK_CHUNK_BYTES)?;
    let storage_owner = storage as *const _ as usize;
    for layer in 0..layers {
        let window_program = programs.main_continuation_window_layer(layer);
        let continuation_program = programs.continuation_layer(layer);
        assert_eq!(window_program.layer, continuation_program.layer);
        assert_eq!(
            window_program.coefficients,
            continuation_program.coefficients
        );
        assert_eq!(
            window_program.sources.len(),
            continuation_program.coefficients.sources.len()
        );
        assert!(window_program
            .sources
            .iter()
            .enumerate()
            .all(|(index, source)| {
                source.id.0 as usize == index
                    && source.origin == continuation_program.coefficients.sources[index]
            }));
        let raw_source_count = window_program
            .sources
            .iter()
            .filter(|source| family_read_place(source.raw_family, source.raw_column).is_some())
            .count();
        assert!(raw_source_count > 0, "Task 8 layer retained no raw sources");
        let expected_source_count = window_program.sources.len();
        let procedural_source_count = window_program.sources.len() - raw_source_count;
        let window_sources = schedule_source_identity(
            storage,
            window_program,
            &mut readback_scratch,
            callbacks,
            context,
        )?;
        let legacy_sources = schedule_source_identity(
            storage,
            window_program,
            &mut readback_scratch,
            callbacks,
            context,
        )?;
        let source_table: Arc<Mutex<Option<Vec<Task8SourceIdentityRecord>>>> =
            Arc::new(Mutex::new(None));
        let callback_source_table = Arc::clone(&source_table);
        let callback_source_accumulator = Arc::clone(&accumulator);
        let source_payload = Mutex::new(Some((window_sources, legacy_sources)));
        callbacks.schedule(
            move || {
                let (window_sources, legacy_sources) = source_payload
                    .lock()
                    .expect("Task 8 scheduled source payload mutex poisoned")
                    .take()
                    .expect("Task 8 scheduled source payload consumed twice");
                let window_sources: Vec<_> = window_sources
                    .into_iter()
                    .map(ScheduledSourceIdentityRecord::materialize)
                    .collect();
                let legacy_sources: Vec<_> = legacy_sources
                    .into_iter()
                    .map(ScheduledSourceIdentityRecord::materialize)
                    .collect();
                assert_source_records_nonvacuous(&window_sources, raw_source_count);
                assert_eq!(window_sources, legacy_sources);
                if window_sources.len() > 1 {
                    assert!(
                        window_sources
                            .iter()
                            .map(|record| record.backing_base)
                            .collect::<BTreeSet<_>>()
                            .len()
                            < window_sources.len(),
                        "Task 8 consolidated storage regressed to one allocation per raw source"
                    );
                }
                {
                    let mut state = callback_source_accumulator
                        .lock()
                        .expect("Task 8 source-census accumulator mutex poisoned");
                    assert!(state
                        .source_id_census
                        .insert(
                            layer,
                            window_sources
                                .iter()
                                .map(|record| record.source.0)
                                .collect(),
                        )
                        .is_none());
                    assert!(state
                        .source_backing_census
                        .insert(
                            layer,
                            window_sources
                                .iter()
                                .map(|record| record.backing_base)
                                .collect::<BTreeSet<_>>()
                                .len(),
                        )
                        .is_none());
                }
                let previous = callback_source_table
                    .lock()
                    .expect("Task 8 source-table mutex poisoned")
                    .replace(window_sources);
                assert!(previous.is_none(), "Task 8 source table materialized twice");
            },
            context.get_exec_stream(),
        )?;

        let capacity = run_first_pass_legacy_capacity_probe(
            storage,
            window_program,
            continuation_program,
            inits_and_teardowns_top_bits,
            folding_steps,
            &point_host,
            callbacks,
            context,
        )?;
        assert_eq!(capacity.overlap_event.owners.len(), 2);
        {
            let mut state = accumulator
                .lock()
                .expect("Task 8 differential accumulator mutex poisoned");
            state.capacity_overlap_rows += 1;
            state.source_table_identity_rows += 1;
            state.masks.insert(window_program.shape.bits());
            state.max_sources = state.max_sources.max(window_program.sources.len());
            state.procedural_source_records += procedural_source_count;
            if capacity.publication_bytes > 2usize << 30 {
                state.capacity_heavy_layers.push(layer);
                state
                    .capacity_publication_bytes
                    .push(capacity.publication_bytes);
                state.capacity_overlap_live_bytes.push(
                    capacity
                        .overlap_event
                        .owners
                        .iter()
                        .map(|owner| owner.2)
                        .sum(),
                );
                state
                    .capacity_overlap_owner_counts
                    .push(capacity.overlap_event.owners.len());
                state
                    .capacity_physical_peak_bytes
                    .push(capacity.memory.physical_backing_peak_bytes);
                state
                    .capacity_logical_peak_bytes
                    .push(capacity.memory.logical_live_peak_bytes);
            }
        }
        for pass_index in 0..usize::from(plan) {
            let start_round = 3 * (pass_index + 1);
            let window = run_window_arm(
                storage,
                window_program,
                continuation_program,
                inits_and_teardowns_top_bits,
                folding_steps,
                start_round,
                &point_host,
                &mut readback_scratch,
                callbacks,
                context,
            )?;
            let (legacy, source_columns, shape, adoption) = run_legacy_arm(
                storage,
                window_program,
                continuation_program,
                inits_and_teardowns_top_bits,
                folding_steps,
                start_round,
                &point_host,
                &mut readback_scratch,
                callbacks,
                context,
            )?;
            let callback_accumulator = Arc::clone(&accumulator);
            let callback_source_table = Arc::clone(&source_table);
            let coordinate_payload =
                Mutex::new(Some((window, legacy, source_columns, shape, adoption)));
            callbacks.schedule(
                move || {
                    let (window, legacy, source_columns, shape, adoption) = coordinate_payload
                        .lock()
                        .expect("Task 8 coordinate payload mutex poisoned")
                        .take()
                        .expect("Task 8 coordinate payload consumed twice");
                    let (adoption_mutation_checks, adoption_families) =
                        validate_adoption_mutations(&adoption);
                    let sources = callback_source_table
                        .lock()
                        .expect("Task 8 source-table mutex poisoned")
                        .as_ref()
                        .expect("Task 8 source-table callback did not run")
                        .clone();
                    let (window, window_memory, window_allocations, window_live_mutations) =
                        window.materialize();
                    let (mut legacy, legacy_memory, legacy_allocations, legacy_live_mutations) =
                        legacy.materialize();
                    assert!(legacy_live_mutations.materialize().is_empty());
                    let raw_publication = std::mem::take(&mut legacy.publication);
                    assert_eq!(source_columns.len(), expected_source_count);
                    assert!(source_columns
                        .iter()
                        .enumerate()
                        .all(|(index, (source, _))| source.0 as usize == index));
                    legacy.publication = canonicalize_legacy_publication(
                        &raw_publication,
                        &source_columns,
                        shape.columns,
                        shape.column_elems,
                    )
                    .unwrap_or_else(|error| panic!("Task 8 legacy canonicalization: {error:?}"));
                    assert_eq!(window_memory.start, legacy_memory.start);
                    assert_eq!(window_memory.return_to_entry, window_memory.start);
                    assert_eq!(legacy_memory.return_to_entry, legacy_memory.start);
                    assert!(
                        window_memory.physical_backing_peak_bytes
                            <= legacy_memory.physical_backing_peak_bytes,
                        "Task 8 window arm increased physical backing peak"
                    );
                    assert!(
                        window_memory.logical_live_peak_bytes
                            <= legacy_memory.logical_live_peak_bytes,
                        "Task 8 window arm increased corrected logical peak"
                    );
                    let semantic_comparisons = compare_observations(&window, &legacy)
                        .unwrap_or_else(|error| {
                            panic!("Task 8 prepared-state differential mismatch: {error:?}")
                        });
                    let comparator_field_coverage_checks =
                        run_comparator_field_coverage_checks(&window, &legacy);
                    let mut mutation_checks = 0usize;
                    let (live_mutation_checks, mut mutation_families) =
                        validate_live_observation_mutations(
                            &window,
                            &legacy,
                            window_live_mutations,
                        );
                    mutation_checks += live_mutation_checks;
                    mutation_checks += adoption_mutation_checks;
                    mutation_families.extend(adoption_families);
                    let displaced = source_columns
                        .iter()
                        .filter(|(source, column)| source.0 as usize != *column)
                        .count();
                    if source_columns.len() > 1 {
                        let mut duplicate = source_columns.clone();
                        duplicate[0].0 = duplicate[1].0;
                        assert!(matches!(
                            canonicalize_legacy_publication(
                                &raw_publication,
                                &duplicate,
                                shape.columns,
                                shape.column_elems,
                            ),
                            Err(LegacyPublicationCanonicalizationError::DuplicateSource { .. })
                        ));
                        mutation_checks += 1;
                        mutation_families.insert("duplicate-missing-canonical-map".to_owned());

                        let mut displaced_columns = source_columns.clone();
                        let mut displacement_rejected = false;
                        'outer: for left in 0..displaced_columns.len() {
                            for right in left + 1..displaced_columns.len() {
                                displaced_columns.swap(left, right);
                                displaced_columns[left].0 = source_columns[left].0;
                                displaced_columns[right].0 = source_columns[right].0;
                                let displaced_publication = canonicalize_legacy_publication(
                                    &raw_publication,
                                    &displaced_columns,
                                    shape.columns,
                                    shape.column_elems,
                                )
                                .expect("Task 8 valid displaced source map was rejected");
                                if displaced_publication != legacy.publication {
                                    displacement_rejected = true;
                                    break 'outer;
                                }
                                displaced_columns = source_columns.clone();
                            }
                        }
                        assert!(
                            displacement_rejected,
                            "Task 8 source-column displacement mutation was not observable"
                        );
                        mutation_checks += 1;
                        mutation_families.insert("source-column-displacement".to_owned());
                    }
                    let mut missing = source_columns.clone();
                    missing.pop();
                    assert!(matches!(
                        canonicalize_legacy_publication(
                            &raw_publication,
                            &missing,
                            shape.columns,
                            shape.column_elems,
                        ),
                        Err(LegacyPublicationCanonicalizationError::MissingSource { .. })
                    ));
                    mutation_checks += 1;
                    mutation_families.insert("duplicate-missing-canonical-map".to_owned());
                    let window_topology_checks = validate_actual_topology_mutations(
                        storage_owner,
                        &sources,
                        &window_allocations,
                    );
                    let legacy_topology_checks = validate_actual_topology_mutations(
                        storage_owner,
                        &sources,
                        &legacy_allocations,
                    );
                    mutation_checks += window_topology_checks.mutation_checks
                        + legacy_topology_checks.mutation_checks;
                    assert!(
                        window_topology_checks.mutation_checks >= 1
                            && legacy_topology_checks.mutation_checks >= 1
                    );
                    mutation_families.insert("duplicate-raw-owner".to_owned());
                    if start_round > 3 {
                        assert_eq!(window_topology_checks.mutation_checks, 2);
                        assert_eq!(legacy_topology_checks.mutation_checks, 2);
                        mutation_families.insert("overlapping-prior-owner".to_owned());
                    }
                    let mut state = callback_accumulator
                        .lock()
                        .expect("Task 8 differential accumulator mutex poisoned");
                    state.start_rounds.insert(start_round);
                    state.max_legacy_displacement = state.max_legacy_displacement.max(displaced);
                    state.semantic_comparisons += semantic_comparisons;
                    state.publication_elements_compared += window.publication.len();
                    state.comparator_field_coverage_checks += comparator_field_coverage_checks;
                    state.mutation_checks += mutation_checks;
                    state.source_identity_records += 2 * sources.len();
                    state.allocation_records += window_allocations.len() + legacy_allocations.len();
                    state.topology_owner_records +=
                        window_topology_checks.owner_records + legacy_topology_checks.owner_records;
                    state
                        .topology_owner_kinds
                        .extend(window_topology_checks.owner_kinds);
                    state
                        .topology_owner_kinds
                        .extend(legacy_topology_checks.owner_kinds);
                    state.topology_coordinates += 1;
                    state.later_start_shared_prior_coordinates += usize::from(start_round > 3);
                    state.multi_source_coordinates += usize::from(source_columns.len() > 1);
                    state.arm_memory_comparisons += 2;
                    state.mutation_families.extend(mutation_families);
                    drop(raw_publication);
                },
                context.get_exec_stream(),
            )?;
        }
    }
    let scratch_owner = Arc::new(Mutex::new(Some(readback_scratch)));
    let callback_scratch_owner = Arc::clone(&scratch_owner);
    let request = Mutex::new(Some(request));
    callbacks.schedule(
        move || {
            let scratch = callback_scratch_owner
                .lock()
                .expect("Task 8 shared readback scratch mutex poisoned")
                .take()
                .expect("Task 8 shared readback scratch retired twice");
            assert_eq!(scratch.len(), TASK8_READBACK_CHUNK_BYTES);
            drop(scratch);
            let mut state = accumulator
                .lock()
                .expect("Task 8 differential accumulator mutex poisoned");
            assert!(state.semantic_comparisons > 0);
            assert!(state.mutation_checks > 0);
            assert_eq!(state.coordinates, state.layers);
            assert_eq!(state.source_table_identity_rows, state.layers);
            assert_eq!(state.start_rounds.len(), usize::from(plan));
            assert_eq!(state.topology_coordinates, state.layers * usize::from(plan));
            assert_eq!(state.arm_memory_comparisons, 2 * state.topology_coordinates);
            let later_coordinates = state.topology_coordinates - state.layers;
            assert_eq!(
                state.later_start_shared_prior_coordinates,
                later_coordinates
            );
            assert_eq!(
                state.allocation_records,
                19 * state.topology_coordinates + 2 * later_coordinates
            );
            assert_eq!(
                state.mutation_checks,
                16 * state.layers + 22 * later_coordinates + 2 * state.multi_source_coordinates
            );
            assert_eq!(
                state.comparator_field_coverage_checks,
                17 * state.topology_coordinates
            );
            assert_eq!(
                state.semantic_comparisons,
                state.publication_elements_compared
                    + TASK8_NON_PUBLICATION_COMPARISONS * state.topology_coordinates
            );
            assert_eq!(state.capacity_overlap_rows, state.layers);
            assert_eq!(state.source_id_census.len(), state.layers);
            assert_eq!(state.source_backing_census.len(), state.layers);
            assert!(state.source_id_census.iter().enumerate().all(
                |(layer, (actual_layer, sources))| {
                    layer == *actual_layer
                        && !sources.is_empty()
                        && sources.iter().copied().collect::<BTreeSet<_>>().len() == sources.len()
                }
            ));
            let raw_sources: usize = state.source_id_census.values().map(Vec::len).sum();
            assert_eq!(
                state.source_identity_records,
                2 * usize::from(plan) * raw_sources
            );
            let backing_owners: usize = state
                .source_backing_census
                .values()
                .map(|backings| 1 + backings)
                .sum();
            assert_eq!(
                state.topology_owner_records,
                state.allocation_records + 2 * usize::from(plan) * backing_owners
            );
            assert_eq!(
                state.topology_owner_kinds,
                [
                    "bank",
                    "challenges",
                    "coefficients",
                    "descriptor",
                    "eq",
                    "partials",
                    "prior_publication",
                    "production_storage",
                    "publication",
                    "raw_backing",
                    "transcript_claim",
                    "transcript_prefactor",
                    "transcript_seed",
                ]
                .into_iter()
                .map(str::to_owned)
                .collect()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_heavy_layers.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_physical_peak_bytes.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_overlap_live_bytes.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_overlap_owner_counts.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_logical_peak_bytes.len()
            );
            assert_eq!(
                state.mutation_families,
                TASK8_MUTATION_FAMILIES
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
            );
            let report = MainContinuationDifferentialReport {
                layers: state.layers,
                coordinates: state.coordinates,
                folding_steps: std::mem::take(&mut state.folding_steps)
                    .into_iter()
                    .collect(),
                start_rounds: std::mem::take(&mut state.start_rounds)
                    .into_iter()
                    .collect(),
                masks: std::mem::take(&mut state.masks).into_iter().collect(),
                max_sources: state.max_sources,
                max_legacy_displacement: state.max_legacy_displacement,
                semantic_comparisons: state.semantic_comparisons,
                publication_elements_compared: state.publication_elements_compared,
                comparator_field_coverage_checks: state.comparator_field_coverage_checks,
                mutation_checks: state.mutation_checks,
                source_table_identity_rows: state.source_table_identity_rows,
                source_identity_records: state.source_identity_records,
                source_id_census: std::mem::take(&mut state.source_id_census)
                    .into_iter()
                    .collect(),
                source_backing_census: std::mem::take(&mut state.source_backing_census)
                    .into_iter()
                    .collect(),
                allocation_records: state.allocation_records,
                topology_owner_records: state.topology_owner_records,
                topology_owner_kinds: std::mem::take(&mut state.topology_owner_kinds)
                    .into_iter()
                    .collect(),
                topology_coordinates: state.topology_coordinates,
                later_start_shared_prior_coordinates: state.later_start_shared_prior_coordinates,
                multi_source_coordinates: state.multi_source_coordinates,
                arm_memory_comparisons: state.arm_memory_comparisons,
                procedural_source_records: state.procedural_source_records,
                mutation_families: std::mem::take(&mut state.mutation_families)
                    .into_iter()
                    .collect(),
                capacity_overlap_rows: state.capacity_overlap_rows,
                capacity_heavy_layers: std::mem::take(&mut state.capacity_heavy_layers),
                capacity_publication_bytes: std::mem::take(&mut state.capacity_publication_bytes),
                capacity_overlap_live_bytes: std::mem::take(&mut state.capacity_overlap_live_bytes),
                capacity_overlap_owner_counts: std::mem::take(
                    &mut state.capacity_overlap_owner_counts,
                ),
                capacity_physical_peak_bytes: std::mem::take(
                    &mut state.capacity_physical_peak_bytes,
                ),
                capacity_logical_peak_bytes: std::mem::take(&mut state.capacity_logical_peak_bytes),
            };
            drop(state);
            request
                .lock()
                .expect("Task 8 terminal request mutex poisoned")
                .take()
                .expect("Task 8 terminal request consumed twice")
                .publish(Ok(report));
        },
        context.get_exec_stream(),
    )?;
    Ok(())
}
