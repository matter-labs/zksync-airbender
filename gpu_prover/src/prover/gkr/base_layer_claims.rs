use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::GKRLayerDescription;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension};

use super::backward::{
    eq_group_tables_len, launch_build_eq_values_from_point, launch_trace_holder_block_partials,
    GpuDimensionReducingKernelSet, GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK,
};
use super::transform::normalize_layer_for_gpu;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor, UnsafeMutAccessor,
};
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::proof_layout::{ProofLayout, WhirBaseLayerKind};
use crate::prover::trace_holder::TraceHolder;

cuda_kernel!(
    EvalVirtualSetupClaims,
    ab_gkr_eval_virtual_setup_claims_e4_kernel(
        claim_point: *const E4,
        trace_len_log2: u32,
        output: *mut E4,
    )
);

/// Number of E4 outputs produced by the virtual-setup-claims kernel:
/// [RangeCheck16, RangeCheckTimestamp, InitsAndTeardownsLow, InitsAndTeardownsHigh].
pub(crate) const VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN: usize = 4;

/// Addresses corresponding to each entry in the kernel's virtual-setup output.
const VIRTUAL_SETUP_ADDRESSES: [GKRAddress; VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN] = [
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
];

/// Launches the single-thread kernel that evaluates the four virtual setup
/// polynomials at `claim_point` (length `trace_len_log2`) and writes the
/// `[RangeCheck16, RangeCheckTimestamp, InitsAndTeardownsLow,
/// InitsAndTeardownsHigh]` E4 values into `output`.
fn launch_eval_virtual_setup_claims(
    claim_point: *const E4,
    trace_len_log2: u32,
    output: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(1, 1, context.get_exec_stream());
    let args = EvalVirtualSetupClaimsArguments::new(claim_point, trace_len_log2, output);
    EvalVirtualSetupClaimsFunction::default().launch(&config, &args)
}

/// Production view onto the post-aggregation state. Holds accessors into the
/// pinned `BaseLayerExtrasPlan` buffers owned by the keepalive — never copies
/// the values to the host-resident heap. Consumers (the post-aggregation
/// callback and the final D2H callback) iterate the values sequentially.
#[derive(Copy, Clone)]
pub(crate) struct GpuGKRBaseLayerTailOutput<E> {
    pub(crate) extra_evaluations_addresses: UnsafeAccessor<[GKRAddress]>,
    pub(crate) extra_evaluations_values: UnsafeAccessor<[E]>,
}

/// Test convenience snapshot: owns its data so `wait()` can drop the
/// keepalive on return.
#[derive(Clone)]
pub(crate) struct GpuGKRBaseLayerTailSnapshot<E> {
    pub(crate) extra_evaluations_addresses: Box<[GKRAddress]>,
    pub(crate) extra_evaluations_values: Box<[E]>,
    pub(crate) virtual_setup_claims: [E; VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN],
    pub(crate) mem_polys_claims: Box<[E]>,
    pub(crate) wit_polys_claims: Box<[E]>,
    pub(crate) setup_polys_claims: Box<[E]>,
}

pub(crate) struct ScheduledBaseLayerClaimsState<E> {
    result: Option<GpuGKRBaseLayerTailOutput<E>>,
}

pub(crate) fn clone_base_layer_extra_evaluations_from_caching_relations<E>(
    shared_state: UnsafeMutAccessor<ScheduledBaseLayerClaimsState<E>>,
) -> BTreeMap<GKRAddress, E>
where
    E: Copy,
{
    let result = unsafe { shared_state.get() }
        .result
        .as_ref()
        .expect("base-layer claims result must be available");
    let addresses = unsafe { result.extra_evaluations_addresses.get() };
    let values = unsafe { result.extra_evaluations_values.get() };
    addresses
        .iter()
        .copied()
        .zip(values.iter().copied())
        .collect()
}

/// Schedule-time-known dense source for one entry in `BaseLayerExtrasPlan`.
/// All caching-relations dependencies that are not already in the layer-1
/// incoming claim set resolve to one of these per-column flat sources; the
/// runtime aggregation callback uses the variant to pick the right accessor.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum DenseSource {
    Memory(usize),
    Witness(usize),
    Setup(usize),
}

impl DenseSource {
    fn from_address(address: GKRAddress) -> Self {
        match address {
            GKRAddress::BaseLayerMemory(offset) => DenseSource::Memory(offset),
            GKRAddress::BaseLayerWitness(offset) => DenseSource::Witness(offset),
            GKRAddress::Setup(offset) => DenseSource::Setup(offset),
            other => {
                panic!("unsupported dense source address {other:?} for cached relation dependency",)
            }
        }
    }
}

/// Schedule-time-known SoA description of the layer-0 caching-relations extras:
/// the addresses whose dependency claims must be filled from per-column dense
/// flats, the matching dense source for each, and a pinned host buffer that
/// receives the values during the aggregation callback. Shape is intentionally
/// GPU-friendly (parallel arrays, schedule-time-fixed length) so this can move
/// off the host as the eventual GPU port lands.
struct BaseLayerExtrasPlan<E> {
    addresses: Box<[GKRAddress]>,
    sources: Box<[DenseSource]>,
    values: HostAllocation<[E]>,
}

impl<E> BaseLayerExtrasPlan<E> {
    fn new(
        layer_desc: &GKRLayerDescription,
        initial_addresses: &[GKRAddress],
        context: &ProverContext,
    ) -> Self {
        let mut already_present: BTreeSet<GKRAddress> = initial_addresses.iter().copied().collect();
        already_present.extend(VIRTUAL_SETUP_ADDRESSES.iter().copied());
        let mut missing: BTreeSet<GKRAddress> = BTreeSet::new();
        for (cached_addr, relation) in layer_desc.cached_relations.iter() {
            debug_assert!(
                already_present.contains(cached_addr),
                "cached relation address {cached_addr:?} must be in layer-1 incoming claims",
            );
            for dep in relation.dependencies() {
                if already_present.contains(&dep) {
                    continue;
                }
                missing.insert(dep);
            }
        }
        let addresses: Box<[GKRAddress]> = missing.iter().copied().collect();
        let sources: Box<[DenseSource]> = addresses
            .iter()
            .map(|addr| DenseSource::from_address(*addr))
            .collect();
        let values = unsafe { context.alloc_host_uninit_slice::<E>(addresses.len()) };
        Self {
            addresses,
            sources,
            values,
        }
    }
}

pub(crate) struct GpuGKRBaseLayerClaimsScheduledExecution<E> {
    _tracing_ranges: Vec<Range>,
    _finish_callbacks: Callbacks<'static>,
    // Pinned D2H readbacks consumed by the deferred aggregation closure below.
    // The closure captures raw accessors, so the underlying chunks must not
    // return to the host pool before the closure is scheduled.
    _virtual_setup_claims_host: HostAllocation<[E]>,
    _mem_polys_claims: HostAllocation<[E]>,
    _wit_polys_claims: HostAllocation<[E]>,
    _setup_polys_claims: HostAllocation<[E]>,
    // Schedule-time-built plan for layer-0 caching-relations extras. The plan
    // owns the pinned `values` buffer; the aggregation callback writes into it
    // through accessors. The plan must outlive every consumer of those
    // accessors (post-aggregation callback + final-D2H callback), so it is
    // parked here.
    _extras_plan: BaseLayerExtrasPlan<E>,
    // Snapshot accessors used by the test convenience `wait()`. Each accessor
    // points into one of the pinned host allocations above; valid only while
    // `self` is alive (i.e. before `wait()` consumes it).
    extras_addresses_accessor: UnsafeAccessor<[GKRAddress]>,
    extras_values_accessor: UnsafeAccessor<[E]>,
    virtual_setup_claims_accessor: UnsafeAccessor<[E]>,
    mem_polys_claims_accessor: UnsafeAccessor<[E]>,
    wit_polys_claims_accessor: UnsafeAccessor<[E]>,
    setup_polys_claims_accessor: UnsafeAccessor<[E]>,
    shared_state: Box<ScheduledBaseLayerClaimsState<E>>,
    // Deferred aggregation closure built by `schedule_prepare_base_layer_claims_with_sources`.
    // Holds the captured pinned-host accessors and `layer_desc`; the caller schedules it
    // exactly once via `schedule_aggregation` after the underlying H2D readbacks complete.
    pending_aggregation: Option<Box<dyn Fn() + Send + Sync + 'static>>,
}

impl<E: Copy + 'static> GpuGKRBaseLayerClaimsScheduledExecution<E> {
    pub(crate) fn shared_state_handle(
        &mut self,
    ) -> UnsafeMutAccessor<ScheduledBaseLayerClaimsState<E>> {
        UnsafeMutAccessor::new(self.shared_state.as_mut())
    }

    /// Schedules the deferred aggregation callback on `stream`. Must be called
    /// exactly once. The callback finalizes `shared_state.result` and runs the
    /// caller-supplied `post_aggregation` closure (e.g. mirror extras into
    /// backward state).
    pub(crate) fn schedule_aggregation(
        &mut self,
        stream: &era_cudart::stream::CudaStream,
    ) -> CudaResult<()> {
        let closure = self
            .pending_aggregation
            .take()
            .expect("aggregation callback already scheduled");
        self._finish_callbacks.schedule(closure, stream)
    }

    /// Hands the deferred aggregation closure to a sibling scheduler (e.g. WHIR
    /// fold setup) so it can be scheduled as part of that scheduler's own
    /// start callback chain. The caller becomes responsible for scheduling
    /// (and keeping the resulting `HostFn` alive); on this struct we no longer
    /// own the closure.
    pub(crate) fn take_pending_aggregation(&mut self) -> Box<dyn Fn() + Send + Sync + 'static> {
        self.pending_aggregation
            .take()
            .expect("aggregation callback already scheduled")
    }

    pub(crate) fn wait(
        mut self,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBaseLayerTailSnapshot<E>> {
        // Test-only path: schedule the aggregation now, then sync.
        if self.pending_aggregation.is_some() {
            self.schedule_aggregation(context.get_exec_stream())?;
        }
        context.get_exec_stream().synchronize()?;
        // SAFETY: stream is synchronized; the host-pinned buffers are stable
        // and the aggregation callback has finished writing them.
        let extra_evaluations_addresses: Box<[GKRAddress]> = unsafe {
            self.extras_addresses_accessor
                .get()
                .iter()
                .copied()
                .collect()
        };
        let extra_evaluations_values: Box<[E]> =
            unsafe { self.extras_values_accessor.get().iter().copied().collect() };
        let virtual_setup_claims = {
            let slice = unsafe { self.virtual_setup_claims_accessor.get() };
            assert_eq!(slice.len(), VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN);
            let mut arr = [slice[0]; VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN];
            arr.copy_from_slice(slice);
            arr
        };
        let mem_polys_claims: Box<[E]> = unsafe {
            self.mem_polys_claims_accessor
                .get()
                .iter()
                .copied()
                .collect()
        };
        let wit_polys_claims: Box<[E]> = unsafe {
            self.wit_polys_claims_accessor
                .get()
                .iter()
                .copied()
                .collect()
        };
        let setup_polys_claims: Box<[E]> = unsafe {
            self.setup_polys_claims_accessor
                .get()
                .iter()
                .copied()
                .collect()
        };
        Ok(GpuGKRBaseLayerTailSnapshot {
            extra_evaluations_addresses,
            extra_evaluations_values,
            virtual_setup_claims,
            mem_polys_claims,
            wit_polys_claims,
            setup_polys_claims,
        })
    }
}

fn schedule_reduce_trace_holder_claims<E>(
    label: &str,
    trace_holder: &TraceHolder<BF>,
    eq_values: &DeviceSlice<E>,
    // B3: when `Some`, `batch_reduce` writes straight into the slab's
    // `whir.{kind}.evals` range (raw `(ptr, len)` resolved by the caller via
    // `proof_layout.whir_base_evals_device_mut`). Eliminates the standalone
    // `claims_device` allocation and the post-D2H slab H2D-back loop. When
    // `None` (test paths), a fallback device buffer is allocated.
    slab_claims_dst: Option<(*mut E, usize)>,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E]>>
where
    E: GpuDimensionReducingKernelSet + Field + 'static,
{
    let trace_len = 1usize << trace_holder.log_domain_size;
    assert_eq!(eq_values.len(), trace_len);
    assert!(trace_len <= u32::MAX as usize);
    assert!(trace_len <= i32::MAX as usize);
    assert_eq!(
        trace_len % 4,
        0,
        "base-layer claims require trace lengths divisible by 4"
    );
    let columns_count = trace_holder.columns_count;
    assert!(columns_count <= u32::MAX as usize);
    assert!(columns_count <= i32::MAX as usize);
    if columns_count == 0 {
        return Ok(unsafe { context.alloc_host_uninit_slice(0) });
    }

    let blocks_count = context.get_device_properties().sm_count;
    assert!(blocks_count > 0, "device must expose at least one SM");
    assert!(blocks_count <= u32::MAX as usize);
    assert!(blocks_count <= i32::MAX as usize);

    let mut block_partials =
        context.alloc(columns_count * blocks_count, AllocationPlacement::BestFit)?;
    let reduction_temp_bytes = get_batch_reduce_temp_storage_bytes::<E>(
        ReduceOperation::Sum,
        columns_count as i32,
        blocks_count as i32,
    )?;
    let mut reduction_temp = context
        .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
            reduction_temp_bytes,
            AllocationPlacement::BestFit,
        )?;
    let stream = context.get_exec_stream();
    let reduction_range = Range::new(format!("gkr.base_layer_claims.reduce.{label}"))?;
    reduction_range.start(stream)?;
    let raw_values = trace_holder.get_hypercube_evals();
    for column_start in (0..columns_count).step_by(GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK) {
        let chunk_cols =
            (columns_count - column_start).min(GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK);
        launch_trace_holder_block_partials(
            raw_values.as_ptr(),
            eq_values.as_ptr(),
            block_partials.as_mut_ptr(),
            trace_len,
            column_start,
            chunk_cols,
            blocks_count,
            context,
        )?;
    }
    let block_partials_matrix = DeviceMatrix::new(&block_partials, blocks_count);

    // Resolve `batch_reduce`'s output destination — slab subslice (B3) or a
    // per-call fallback allocation. The slab's `whir.{kind}.evals` range is
    // held alive by `_proof_slab` keepalive across all base-layer reductions
    // and the subsequent D2H. The fallback is dropped at the end of this
    // function, which is fine because the D2H is already scheduled by then.
    let mut fallback_claims_device: Option<DeviceAllocation<E>> = None;
    let claims_dst_ptr: *mut E = if let Some((slab_ptr, slab_len)) = slab_claims_dst {
        assert_eq!(
            slab_len, columns_count,
            "slab whir.{label}.evals length must match trace_holder.columns_count",
        );
        slab_ptr
    } else {
        let alloc: DeviceAllocation<E> =
            context.alloc(columns_count, AllocationPlacement::BestFit)?;
        let ptr = alloc.as_ptr() as *mut E;
        fallback_claims_device = Some(alloc);
        ptr
    };
    // SAFETY: see above — the destination memory outlives both the
    // `batch_reduce` kernel and the D2H below; `columns_count` is in-bounds.
    let claims_dst_slice =
        unsafe { DeviceSlice::from_raw_parts_mut(claims_dst_ptr, columns_count) };
    batch_reduce(
        ReduceOperation::Sum,
        &mut reduction_temp,
        &block_partials_matrix,
        claims_dst_slice,
        stream,
    )?;

    let mut host_claims = unsafe { context.alloc_host_uninit_slice(columns_count) };
    // SAFETY: the source memory is the same slab/fallback range we just wrote
    // through `batch_reduce`; both the kernel and the D2H are stream-ordered
    // on `exec_stream`.
    let claims_src_slice =
        unsafe { DeviceSlice::from_raw_parts(claims_dst_ptr as *const E, columns_count) };
    memory_copy_async(&mut host_claims, claims_src_slice, stream)?;
    reduction_range.end(stream)?;
    tracing_ranges.push(reduction_range);

    drop(fallback_claims_device);
    Ok(host_claims)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_prepare_base_layer_claims_with_sources<E>(
    mut layer_desc: GKRLayerDescription,
    claim_point_device: &DeviceSlice<E>,
    // Schedule-time-known set of layer-1 incoming claim addresses (from
    // `final_claim_layout.addresses` on the backward execution). The plan
    // builder unions this with the four `VIRTUAL_SETUP_ADDRESSES` to compute
    // which caching-relations dependencies are missing and thus need to be
    // sourced from the per-column dense flats at runtime.
    initial_addresses: &[GKRAddress],
    // Runs at the END of the (deferred) aggregation callback. The hot path
    // uses this to mirror `extra_evaluations_*` into `backward_shared_state`
    // (replacing the former separate apply-extras callback). Test paths can
    // pass a no-op closure.
    post_aggregation: impl Fn(&GpuGKRBaseLayerTailOutput<E>) + Send + Sync + 'static,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    // B3: when Some, `batch_reduce` writes the per-column claims directly
    // into the slab's `whir.{setup,memory,witness}.evals` ranges. The pinned
    // host claim vectors are sourced from the slab via the standard D2H
    // (the H2D-back roundtrip is gone). `None` skips slab routing (test
    // paths fall back to per-call device allocations).
    proof_slab: Option<&DeviceAllocation<u8>>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: Copy + GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
{
    normalize_layer_for_gpu(&mut layer_desc);
    for (label, trace_holder) in [
        ("memory", memory_trace_holder),
        ("witness", witness_trace_holder),
    ] {
        assert_eq!(
            trace_holder.log_domain_size, setup_trace_holder.log_domain_size,
            "{label} trace holder must match setup trace length",
        );
    }

    let trace_len = 1usize << setup_trace_holder.log_domain_size;
    let claim_point_len = claim_point_device.len();
    assert_eq!(
        claim_point_len,
        trace_len.trailing_zeros() as usize,
        "base-layer point must match trace length"
    );

    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let schedule_range = Range::new("gkr.base_layer_claims.schedule")?;
    schedule_range.start(stream)?;

    let trace_len_log2 = setup_trace_holder.log_domain_size;

    // Evaluate the four virtual setup polynomial values (RangeCheck16,
    // RangeCheckTimestamp, InitsAndTeardownsLow, InitsAndTeardownsHigh) on
    // device from the device-resident claim_point. The kernel consumes only
    // the device claim_point and writes a 64-byte device buffer that we then
    // D2H into a pinned host slot for the finish callback to read. Replaces
    // the host-side `populate_virtual_setup_claims` E4 polynomial eval and
    // removes the prior `claim_point` D2H entirely.
    //
    // The kernel is E4-only; the trait bounds on `E` resolve to `E4` in
    // practice (`GpuDimensionReducingKernelSet` is implemented only for E4),
    // and we assert layout compatibility before casting.
    debug_assert_eq!(
        std::mem::size_of::<E>(),
        std::mem::size_of::<E4>(),
        "virtual-setup-claims kernel requires E = E4",
    );
    let mut virtual_setup_claims_device = context.alloc::<E>(
        VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN,
        AllocationPlacement::BestFit,
    )?;
    launch_eval_virtual_setup_claims(
        claim_point_device.as_ptr() as *const E4,
        trace_len_log2,
        virtual_setup_claims_device.as_mut_ptr() as *mut E4,
        context,
    )?;
    let mut virtual_setup_claims_host =
        unsafe { context.alloc_host_uninit_slice::<E>(VIRTUAL_SETUP_CLAIMS_OUTPUT_LEN) };
    memory_copy_async(
        &mut virtual_setup_claims_host,
        &virtual_setup_claims_device,
        stream,
    )?;

    let mut eq_group_tables = context.alloc(
        eq_group_tables_len(claim_point_len).max(1),
        AllocationPlacement::BestFit,
    )?;
    let mut eq_values = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    launch_build_eq_values_from_point(
        claim_point_device.as_ptr(),
        0,
        claim_point_len,
        eq_group_tables.as_mut_ptr(),
        eq_values.as_mut_ptr(),
        trace_len,
        context,
    )?;

    // B3: when the slab is provided, route `batch_reduce`'s output of each
    // base-layer column reduction straight into the slab's
    // `whir.{kind}.evals` range. The pinned host claim vectors returned
    // below are then sourced from the slab via the standard D2H — no
    // separate H2D-back loop needed. The size_of guard ensures the *mut E
    // cast is byte-equivalent to the slab's *mut E4 storage.
    if proof_slab.is_some() {
        debug_assert_eq!(
            std::mem::size_of::<E>(),
            std::mem::size_of::<crate::primitives::field::E4>(),
            "base-layer slab routing requires E to be E4-sized",
        );
    }
    let slab_claims_dst = |kind: WhirBaseLayerKind| -> Option<(*mut E, usize)> {
        proof_slab.map(|slab| {
            let (ptr, len) =
                unsafe { proof_layout.whir_base_evals_device_mut(slab.as_ptr() as *mut u8, kind) };
            (ptr as *mut E, len)
        })
    };
    let mem_polys_claims = schedule_reduce_trace_holder_claims(
        "memory",
        memory_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Memory),
        &mut tracing_ranges,
        context,
    )?;
    let wit_polys_claims = schedule_reduce_trace_holder_claims(
        "witness",
        witness_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Witness),
        &mut tracing_ranges,
        context,
    )?;
    let setup_polys_claims = schedule_reduce_trace_holder_claims(
        "setup",
        setup_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Setup),
        &mut tracing_ranges,
        context,
    )?;

    let mut shared_state = Box::new(ScheduledBaseLayerClaimsState { result: None });
    let shared_state_handle = UnsafeMutAccessor::new(shared_state.as_mut());
    let mem_polys_claims_accessor = mem_polys_claims.get_accessor();
    let wit_polys_claims_accessor = wit_polys_claims.get_accessor();
    let setup_polys_claims_accessor = setup_polys_claims.get_accessor();
    let virtual_setup_claims_accessor = virtual_setup_claims_host.get_accessor();

    // Build the schedule-time SoA plan for the caching-relations extras. The
    // plan owns the pinned `values` buffer and the schedule-time-known
    // `addresses` / `sources` boxes. The aggregation callback fills `values`
    // by indexing into the per-column accessors at the schedule-time-known
    // dense offsets.
    let mut extras_plan = BaseLayerExtrasPlan::<E>::new(&layer_desc, initial_addresses, context);
    drop(layer_desc);
    let extras_addresses_accessor = crate::primitives::context::UnsafeAccessor::<[GKRAddress]>::new(
        extras_plan.addresses.as_ref(),
    );
    let extras_sources_accessor = crate::primitives::context::UnsafeAccessor::<[DenseSource]>::new(
        extras_plan.sources.as_ref(),
    );
    let extras_values_mut_accessor = extras_plan.values.get_mut_accessor();
    let extras_values_accessor = extras_plan.values.get_accessor();
    let shared_state_for_callback = shared_state_handle;
    // Build the aggregation closure but defer its scheduling: the caller calls
    // `schedule_aggregation` on the returned struct, which lets the merged
    // callback land outside `gkr.base_layer_claims.schedule` (e.g. inside
    // `gkr.whir.schedule`). The closure now reads per-column flats by
    // schedule-time-known indices instead of materializing host-side Vecs and
    // walking a BTreeMap; it writes the extras values straight into the
    // pinned `values` buffer in `extras_plan`.
    let pending_aggregation: Box<dyn Fn() + Send + Sync + 'static> = Box::new(move || unsafe {
        let mem = mem_polys_claims_accessor.get();
        let wit = wit_polys_claims_accessor.get();
        let setup = setup_polys_claims_accessor.get();
        let sources = extras_sources_accessor.get();
        let values = extras_values_mut_accessor.get_mut();
        debug_assert_eq!(values.len(), sources.len());
        for (i, source) in sources.iter().enumerate() {
            values[i] = match *source {
                DenseSource::Memory(offset) => mem[offset],
                DenseSource::Witness(offset) => wit[offset],
                DenseSource::Setup(offset) => setup[offset],
            };
        }
        let result = GpuGKRBaseLayerTailOutput {
            extra_evaluations_addresses: extras_addresses_accessor,
            extra_evaluations_values: extras_values_accessor,
        };
        post_aggregation(&result);
        shared_state_for_callback.get_mut().result = Some(result);
    });

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuGKRBaseLayerClaimsScheduledExecution {
        _tracing_ranges: tracing_ranges,
        _finish_callbacks: Callbacks::new(),
        _virtual_setup_claims_host: virtual_setup_claims_host,
        _mem_polys_claims: mem_polys_claims,
        _wit_polys_claims: wit_polys_claims,
        _setup_polys_claims: setup_polys_claims,
        _extras_plan: extras_plan,
        extras_addresses_accessor,
        extras_values_accessor,
        virtual_setup_claims_accessor,
        mem_polys_claims_accessor,
        wit_polys_claims_accessor,
        setup_polys_claims_accessor,
        shared_state,
        pending_aggregation: Some(pending_aggregation),
    })
}

pub(crate) fn schedule_prepare_base_layer_claims<E>(
    layer_desc: &GKRLayerDescription,
    base_layer_point: &[E],
    layer_0_claims: &BTreeMap<GKRAddress, E>,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: Copy + GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
{
    let initial_addresses: Vec<GKRAddress> = layer_0_claims.keys().copied().collect();
    // Test-only convenience: stage the host-provided base layer point through a
    // pinned host buffer + ephemeral device buffer so the new prove-time API
    // (device claim_point in) keeps a single source of truth. Production callers
    // pass a device slice from backward directly.
    let mut point_host = unsafe { context.alloc_host_uninit_slice::<E>(base_layer_point.len()) };
    unsafe {
        point_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(base_layer_point);
    }
    let mut point_device =
        context.alloc::<E>(base_layer_point.len(), AllocationPlacement::BestFit)?;
    memory_copy_async(&mut point_device, &point_host, context.get_exec_stream())?;
    schedule_prepare_base_layer_claims_with_sources(
        layer_desc.clone(),
        &point_device,
        &initial_addresses,
        |_| {},
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
        None,
        proof_layout,
        context,
    )
}

pub(crate) fn prepare_base_layer_claims<E>(
    layer_desc: &GKRLayerDescription,
    base_layer_point: &[E],
    layer_0_claims: &BTreeMap<GKRAddress, E>,
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerTailSnapshot<E>>
where
    E: Copy + GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
{
    schedule_prepare_base_layer_claims(
        layer_desc,
        base_layer_point,
        layer_0_claims,
        setup_trace_holder,
        memory_trace_holder,
        witness_trace_holder,
        proof_layout,
        context,
    )?
    .wait(context)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
    use cs::gkr_compiler::GKRLayerDescription;
    use era_cudart::memory::memory_copy_async;
    use field::{Field, FieldExtension, PrimeField};
    use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
    use prover::gkr::virtual_polys::init_and_teardown_base::evaluate_virtual_inits_and_teardowns_base_address_setup_polys;
    use prover::gkr::virtual_polys::range_check::evaluate_virtual_range_check_setup_poly;
    use serial_test::serial;
    use worker::Worker;

    use super::prepare_base_layer_claims;
    use crate::primitives::field::{BF, E4};
    use crate::prover::test_utils::make_test_context;
    use crate::prover::trace_holder::{TraceHolder, TreesCacheMode};

    fn evaluate_base_poly_with_eq<F: PrimeField, E: FieldExtension<F> + Field>(
        values: &[F],
        eq: &[E],
    ) -> E {
        assert_eq!(values.len(), eq.len());
        let mut result = E::ZERO;
        for (value, eq_value) in values.iter().zip(eq.iter()) {
            let mut term = *eq_value;
            term.mul_assign_by_base(value);
            result.add_assign(&term);
        }
        result
    }

    fn make_trace_holder(
        values: &[BF],
        columns_count: usize,
        trace_len: usize,
        context: &crate::primitives::context::ProverContext,
    ) -> TraceHolder<BF> {
        let mut trace_holder = TraceHolder::<BF>::new(
            trace_len.trailing_zeros(),
            0,
            0,
            0,
            columns_count,
            TreesCacheMode::CacheNone,
            context,
        )
        .unwrap();
        memory_copy_async(
            trace_holder.get_uninit_hypercube_evals_mut(),
            values,
            context.get_exec_stream(),
        )
        .unwrap();
        trace_holder
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn base_layer_claims_match_cpu() {
        let trace_len = 1usize << 19;
        let trace_len_log2 = trace_len.trailing_zeros();
        let memory_columns = 3usize;
        let witness_columns = 2usize;
        let setup_columns = 4usize;
        let context = make_test_context(256, 64);

        let memory_values: Vec<_> = (0..memory_columns * trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 1))
            .collect();
        let witness_values: Vec<_> = (0..witness_columns * trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 101))
            .collect();
        let setup_values: Vec<_> = (0..setup_columns * trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 1001))
            .collect();

        let memory_trace_holder =
            make_trace_holder(&memory_values, memory_columns, trace_len, &context);
        let witness_trace_holder =
            make_trace_holder(&witness_values, witness_columns, trace_len, &context);
        let setup_trace_holder =
            make_trace_holder(&setup_values, setup_columns, trace_len, &context);

        let base_layer_point: Vec<_> = (0..trace_len_log2)
            .map(|i| E4::from_base(BF::from_u32_unchecked(2 * i + 3)))
            .collect();
        let layer_desc = GKRLayerDescription {
            layer: 1,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: Vec::new(),
        };

        let proof_layout = crate::prover::proof_layout::ProofLayout::new(
            &crate::prover::proof_layout::placeholder_inputs_for_prove(),
        );
        let output = prepare_base_layer_claims(
            &layer_desc,
            &base_layer_point,
            &BTreeMap::new(),
            &setup_trace_holder,
            &memory_trace_holder,
            &witness_trace_holder,
            &proof_layout,
            &context,
        )
        .unwrap();

        let worker = Worker::new();
        let eq_precomputed = make_eq_poly_in_full(&base_layer_point, &worker);
        let eq_at_z = eq_precomputed.last().unwrap();

        let expected_memory: Vec<_> = (0..memory_columns)
            .map(|column| {
                evaluate_base_poly_with_eq::<BF, E4>(
                    &memory_values[column * trace_len..(column + 1) * trace_len],
                    eq_at_z,
                )
            })
            .collect();
        let expected_witness: Vec<_> = (0..witness_columns)
            .map(|column| {
                evaluate_base_poly_with_eq::<BF, E4>(
                    &witness_values[column * trace_len..(column + 1) * trace_len],
                    eq_at_z,
                )
            })
            .collect();
        let expected_setup: Vec<_> = (0..setup_columns)
            .map(|column| {
                evaluate_base_poly_with_eq::<BF, E4>(
                    &setup_values[column * trace_len..(column + 1) * trace_len],
                    eq_at_z,
                )
            })
            .collect();
        let expected_range_16 = evaluate_virtual_range_check_setup_poly::<BF, E4, 16>(
            &base_layer_point,
            trace_len_log2,
        );
        let expected_timestamp = evaluate_virtual_range_check_setup_poly::<
            BF,
            E4,
            TIMESTAMP_COLUMNS_NUM_BITS,
        >(&base_layer_point, trace_len_log2);
        let (expected_inits_low, expected_inits_high) =
            evaluate_virtual_inits_and_teardowns_base_address_setup_polys::<BF, E4, 2>(
                &base_layer_point,
                trace_len_log2,
            );

        assert_eq!(output.virtual_setup_claims[0], expected_range_16);
        assert_eq!(output.virtual_setup_claims[1], expected_timestamp);
        assert_eq!(output.virtual_setup_claims[2], expected_inits_low);
        assert_eq!(output.virtual_setup_claims[3], expected_inits_high);
        assert_eq!(output.mem_polys_claims.as_ref(), expected_memory.as_slice());
        assert_eq!(
            output.wit_polys_claims.as_ref(),
            expected_witness.as_slice()
        );
        assert_eq!(
            output.setup_polys_claims.as_ref(),
            expected_setup.as_slice(),
        );
        // No cached relations in this test case, so the schedule-time extras
        // plan is empty.
        assert!(output.extra_evaluations_addresses.is_empty());
        assert!(output.extra_evaluations_values.is_empty());

        for (column, expected) in expected_memory.iter().copied().enumerate() {
            assert_eq!(output.mem_polys_claims[column], expected);
        }
        for (column, expected) in expected_witness.iter().copied().enumerate() {
            assert_eq!(output.wit_polys_claims[column], expected);
        }
        for (column, expected) in expected_setup.iter().copied().enumerate() {
            assert_eq!(output.setup_polys_claims[column], expected);
        }
    }
}
