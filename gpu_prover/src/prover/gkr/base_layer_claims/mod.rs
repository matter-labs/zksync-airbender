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
use crate::prover::proof::layout::{ProofLayout, WhirBaseLayerKind};
use crate::prover::trace::holder::TraceHolder;

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

/// Production view onto the post-aggregation state. Addresses/sources are
/// schedule-time metadata owned by the keepalive; fallback test paths also
/// carry a host values accessor populated from dense claim readbacks.
#[derive(Copy, Clone)]
pub(crate) struct GpuGKRBaseLayerTailOutput<E> {
    pub(crate) extra_evaluations_addresses: UnsafeAccessor<[GKRAddress]>,
    extra_evaluations_sources: UnsafeAccessor<[DenseSource]>,
    _marker: std::marker::PhantomData<E>,
}

pub(crate) struct ScheduledBaseLayerClaimsState<E> {
    result: Option<GpuGKRBaseLayerTailOutput<E>>,
}

pub(crate) fn clone_base_layer_extra_evaluations_from_slab(
    shared_state: UnsafeMutAccessor<ScheduledBaseLayerClaimsState<E4>>,
    proof_layout: &ProofLayout,
    slab: &[u8],
) -> BTreeMap<GKRAddress, E4> {
    let result = unsafe { shared_state.get() }
        .result
        .as_ref()
        .expect("base-layer claims result must be available");
    let addresses = unsafe { result.extra_evaluations_addresses.get() };
    let sources = unsafe { result.extra_evaluations_sources.get() };
    debug_assert_eq!(addresses.len(), sources.len());
    addresses
        .iter()
        .copied()
        .zip(
            sources
                .iter()
                .copied()
                .map(|source| source.read_from_slab(proof_layout, slab)),
        )
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

    fn read_from_slab(self, proof_layout: &ProofLayout, slab: &[u8]) -> E4 {
        match self {
            DenseSource::Memory(offset) => {
                proof_layout.whir_base_evals_host(slab, WhirBaseLayerKind::Memory)[offset]
            }
            DenseSource::Witness(offset) => {
                proof_layout.whir_base_evals_host(slab, WhirBaseLayerKind::Witness)[offset]
            }
            DenseSource::Setup(offset) => {
                proof_layout.whir_base_evals_host(slab, WhirBaseLayerKind::Setup)[offset]
            }
        }
    }

    unsafe fn device_ptr<E>(
        self,
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
    ) -> *const E {
        let slab_base = proof_slab.as_ptr() as *mut u8;
        let (base, len) = match self {
            DenseSource::Memory(offset) => {
                let (ptr, len) =
                    proof_layout.whir_base_evals_device_mut(slab_base, WhirBaseLayerKind::Memory);
                assert!(offset < len, "memory dense source offset out of slab range");
                (ptr, len)
            }
            DenseSource::Witness(offset) => {
                let (ptr, len) =
                    proof_layout.whir_base_evals_device_mut(slab_base, WhirBaseLayerKind::Witness);
                assert!(
                    offset < len,
                    "witness dense source offset out of slab range"
                );
                (ptr, len)
            }
            DenseSource::Setup(offset) => {
                let (ptr, len) =
                    proof_layout.whir_base_evals_device_mut(slab_base, WhirBaseLayerKind::Setup);
                assert!(offset < len, "setup dense source offset out of slab range");
                (ptr, len)
            }
        };
        let offset = match self {
            DenseSource::Memory(offset)
            | DenseSource::Witness(offset)
            | DenseSource::Setup(offset) => offset,
        };
        debug_assert!(offset < len);
        base.add(offset) as *const E
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
    values: Option<HostAllocation<[E]>>,
}

impl<E> BaseLayerExtrasPlan<E> {
    fn new(
        layer_desc: &GKRLayerDescription,
        initial_addresses: &[GKRAddress],
        allocate_host_values: bool,
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
        let values = allocate_host_values
            .then(|| unsafe { context.alloc_host_uninit_slice::<E>(addresses.len()) });
        Self {
            addresses,
            sources,
            values,
        }
    }
}

#[allow(dead_code)]
pub(crate) struct GpuGKRBaseLayerClaimsScheduledExecution<E> {
    _tracing_ranges: Vec<Range>,
    _finish_callbacks: Callbacks<'static>,
    // Fallback/test pinned D2H readbacks consumed by the deferred aggregation
    // closure below. Production slab routing keeps these as `None`.
    _virtual_setup_claims_host: Option<HostAllocation<[E]>>,
    _mem_polys_claims: Option<HostAllocation<[E]>>,
    _wit_polys_claims: Option<HostAllocation<[E]>>,
    _setup_polys_claims: Option<HostAllocation<[E]>>,
    // Production device gather of cached-relation extras. It is committed into
    // the final backward seed on-device, so it must live until stream work ends.
    _extras_values_device: Option<DeviceAllocation<E>>,
    // Schedule-time-built plan for layer-0 caching-relations extras. The plan
    // owns the optional fallback `values` buffer and the production metadata.
    // The plan must outlive every consumer of those accessors, so it is parked
    // here.
    _extras_plan: BaseLayerExtrasPlan<E>,
    // Snapshot accessors used by the test convenience `wait()`. Each accessor
    // points into one of the pinned host allocations above; valid only while
    // `self` is alive (i.e. before `wait()` consumes it).
    extras_addresses_accessor: UnsafeAccessor<[GKRAddress]>,
    extras_values_accessor: Option<UnsafeAccessor<[E]>>,
    virtual_setup_claims_accessor: Option<UnsafeAccessor<[E]>>,
    mem_polys_claims_accessor: Option<UnsafeAccessor<[E]>>,
    wit_polys_claims_accessor: Option<UnsafeAccessor<[E]>>,
    setup_polys_claims_accessor: Option<UnsafeAccessor<[E]>>,
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
    readback_to_host: bool,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<Option<HostAllocation<[E]>>>
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
        return Ok(readback_to_host.then(|| unsafe { context.alloc_host_uninit_slice(0) }));
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

    let host_claims = if readback_to_host {
        let mut host_claims = unsafe { context.alloc_host_uninit_slice(columns_count) };
        // SAFETY: the source memory is the same slab/fallback range we just wrote
        // through `batch_reduce`; both the kernel and the D2H are stream-ordered
        // on `exec_stream`.
        let claims_src_slice =
            unsafe { DeviceSlice::from_raw_parts(claims_dst_ptr as *const E, columns_count) };
        memory_copy_async(&mut host_claims, claims_src_slice, stream)?;
        Some(host_claims)
    } else {
        None
    };
    reduction_range.end(stream)?;
    tracing_ranges.push(reduction_range);

    drop(fallback_claims_device);
    Ok(host_claims)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_prepare_base_layer_claims_with_sources<E>(
    layer_desc: GKRLayerDescription,
    claim_point_device: &DeviceSlice<E>,
    // Schedule-time-known set of layer-1 incoming claim addresses (from
    // `final_claim_layout.addresses` on the backward execution). The plan
    // builder unions this with the four `VIRTUAL_SETUP_ADDRESSES` to compute
    // which caching-relations dependencies are missing and thus need to be
    // sourced from the per-column dense flats at runtime.
    initial_addresses: &[GKRAddress],
    setup_trace_holder: &TraceHolder<BF>,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    // When Some, `batch_reduce` writes the per-column claims directly into the
    // slab's `whir.{setup,memory,witness}.evals` ranges. Cached-relation extras
    // are gathered from those slab ranges on device; `None` keeps the
    // host-readback fallback used by tests.
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    // Production path: when present, cached-relation extras are gathered from
    // the slab-resident base evals and committed into this final backward seed
    // on-device. Fallback/test paths pass `None` and use host readbacks.
    final_device_seed: Option<&mut DeviceAllocation<u32>>,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: Copy + GpuDimensionReducingKernelSet + FieldExtension<BF> + Field + 'static,
{
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

    let production_slab_path = proof_slab.is_some();
    let virtual_setup_claims_host = if production_slab_path {
        None
    } else {
        // Test/fallback path: evaluate the four virtual setup polynomial values
        // on device and mirror them for the snapshot returned by `wait()`.
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
        Some(virtual_setup_claims_host)
    };

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

    // When the slab is provided, route `batch_reduce`'s output of each
    // base-layer column reduction straight into the slab's `whir.{kind}.evals`
    // range. Production does not mirror those dense vectors here; cached
    // relation extras are gathered from the slab on device below, and final
    // proof parsing reads the same slab ranges after the terminal D2H.
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
        !production_slab_path,
        &mut tracing_ranges,
        context,
    )?;
    let wit_polys_claims = schedule_reduce_trace_holder_claims(
        "witness",
        witness_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Witness),
        !production_slab_path,
        &mut tracing_ranges,
        context,
    )?;
    let setup_polys_claims = schedule_reduce_trace_holder_claims(
        "setup",
        setup_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Setup),
        !production_slab_path,
        &mut tracing_ranges,
        context,
    )?;

    let mut shared_state = Box::new(ScheduledBaseLayerClaimsState { result: None });
    let shared_state_handle = UnsafeMutAccessor::new(shared_state.as_mut());
    let mem_polys_claims_accessor = mem_polys_claims.as_ref().map(HostAllocation::get_accessor);
    let wit_polys_claims_accessor = wit_polys_claims.as_ref().map(HostAllocation::get_accessor);
    let setup_polys_claims_accessor = setup_polys_claims
        .as_ref()
        .map(HostAllocation::get_accessor);
    let virtual_setup_claims_accessor = virtual_setup_claims_host
        .as_ref()
        .map(HostAllocation::get_accessor);

    // Build the schedule-time SoA plan for the caching-relations extras. The
    // production path keeps only `addresses` / `sources` metadata; the fallback
    // path also owns a pinned `values` buffer filled from dense host readbacks.
    let mut extras_plan = BaseLayerExtrasPlan::<E>::new(
        &layer_desc,
        initial_addresses,
        !production_slab_path,
        context,
    );
    drop(layer_desc);
    let extras_addresses_accessor = crate::primitives::context::UnsafeAccessor::<[GKRAddress]>::new(
        extras_plan.addresses.as_ref(),
    );
    let extras_sources_accessor = crate::primitives::context::UnsafeAccessor::<[DenseSource]>::new(
        extras_plan.sources.as_ref(),
    );
    let extras_values_mut_accessor = extras_plan
        .values
        .as_mut()
        .map(HostAllocation::get_mut_accessor);
    let extras_values_accessor = extras_plan
        .values
        .as_ref()
        .map(HostAllocation::get_accessor);
    let shared_state_for_callback = shared_state_handle;
    let mut extras_values_device = None;
    if production_slab_path {
        let proof_slab = proof_slab.expect("production slab path requires slab");
        let final_device_seed =
            final_device_seed.expect("production slab path requires final device seed");
        if !extras_plan.sources.is_empty() {
            assert_eq!(
                std::mem::size_of::<E>(),
                std::mem::size_of::<E4>(),
                "base-layer extras gather requires E = E4",
            );
            let src_ptrs: Vec<u64> = extras_plan
                .sources
                .iter()
                .copied()
                .map(|source| unsafe { source.device_ptr::<E>(proof_slab, proof_layout) as u64 })
                .collect();
            let mut d_values =
                context.alloc::<E>(extras_plan.sources.len(), AllocationPlacement::BestFit)?;
            let d_values_e4 = unsafe { d_values.transmute_mut::<E4>() };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, d_values_e4, 1, stream)?;
            let d_values_u32 = unsafe { d_values.transmute::<u32>() };
            crate::ops::blake2s::transcript_commit(final_device_seed, d_values_u32, stream)?;
            extras_values_device = Some(d_values);
        }
    } else {
        assert!(
            final_device_seed.is_none(),
            "fallback base-layer claims must not receive a final device seed"
        );
    }

    // Build the metadata publication closure but defer its scheduling: the
    // caller places it at the front of WHIR start callbacks. Fallback/test
    // paths also fill the host extras values from dense claim readbacks.
    let pending_aggregation: Box<dyn Fn() + Send + Sync + 'static> = Box::new(move || unsafe {
        if let Some(extras_values_mut_accessor) = extras_values_mut_accessor {
            let mem_accessor =
                mem_polys_claims_accessor.expect("host extras aggregation requires memory claims");
            let wit_accessor =
                wit_polys_claims_accessor.expect("host extras aggregation requires witness claims");
            let setup_accessor =
                setup_polys_claims_accessor.expect("host extras aggregation requires setup claims");
            let mem = mem_accessor.get();
            let wit = wit_accessor.get();
            let setup = setup_accessor.get();
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
        }
        let result = GpuGKRBaseLayerTailOutput {
            extra_evaluations_addresses: extras_addresses_accessor,
            extra_evaluations_sources: extras_sources_accessor,
            _marker: std::marker::PhantomData,
        };
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
        _extras_values_device: extras_values_device,
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

#[cfg(test)]
pub(crate) use tests::prepare_base_layer_claims;

#[cfg(test)]
mod tests;
