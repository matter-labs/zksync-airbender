use std::collections::{BTreeMap, BTreeSet};

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::backward::{
    eq_group_tables_len, launch_build_eq_values_from_point, launch_trace_holder_block_partials,
    GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK,
};
use super::BackwardKernels;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::primitives::context::{DeviceAllocation, UnsafeAccessor, UnsafeMutAccessor};
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::proof_layout::{ProofLayout, WhirBaseLayerKind};
use crate::prover::trace::holder::TraceHolder;
use crate::prover::ProverContext;
use crate::upstream::{Field, FieldExtension, GKRAddress, GKRLayerDescription, VirtualSetupPoly};

/// Addresses for the four virtual setup polynomials that every layer adds to
/// its claim set: [RangeCheck16, RangeCheckTimestamp, InitsAndTeardownsLow,
/// InitsAndTeardownsHigh].
const VIRTUAL_SETUP_ADDRESSES: [GKRAddress; 4] = [
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
];

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
/// flats and the matching dense source for each. Shape is intentionally
/// GPU-friendly (parallel arrays, schedule-time-fixed length) so this can move
/// off the host as the eventual GPU port lands.
struct BaseLayerExtrasPlan<E> {
    addresses: Box<[GKRAddress]>,
    sources: Box<[DenseSource]>,
    _marker: std::marker::PhantomData<E>,
}

impl<E> BaseLayerExtrasPlan<E> {
    fn new(
        layer_desc: &GKRLayerDescription,
        initial_addresses: &[GKRAddress],
        _context: &ProverContext,
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
        Self {
            addresses,
            sources,
            _marker: std::marker::PhantomData,
        }
    }
}

#[allow(dead_code)]
pub(crate) struct GpuGKRBaseLayerClaimsScheduledExecution<E> {
    _tracing_ranges: Vec<Range>,
    // Device gather of cached-relation extras. It is committed into the final
    // backward seed on-device, so it must live until stream work ends.
    _extras_values_device: Option<DeviceAllocation<E>>,
    // Schedule-time-built plan for layer-0 caching-relations extras. The plan
    // owns the metadata; addresses/sources accessors point into it.
    _extras_plan: BaseLayerExtrasPlan<E>,
    // Schedule-time-known set of extras addresses; carried in the published
    // tail output so the terminal parser can pair each address with the
    // matching slab-resident eval read at parse time.
    extras_addresses_accessor: UnsafeAccessor<[GKRAddress]>,
    shared_state: Box<ScheduledBaseLayerClaimsState<E>>,
    // Deferred metadata-publication closure built by
    // `schedule_prepare_base_layer_claims_with_sources`. The caller schedules
    // it exactly once at the front of WHIR start callbacks.
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

    /// Release the device gather of cached-relation extras. It has been
    /// committed into the final backward seed on-device by prove-end, so the
    /// reservation frees stream-ordered. The schedule-time host metadata (the
    /// extras plan + addresses accessor + the `result` sink read by the
    /// terminal callback) stays.
    pub(crate) fn release_device_buffers(&mut self) {
        self._extras_values_device = None;
    }
}

fn schedule_reduce_trace_holder_claims<E>(
    label: &str,
    trace_holder: &TraceHolder<BF>,
    eq_values: &DeviceSlice<E>,
    // B3: `batch_reduce` writes straight into the slab's `whir.{kind}.evals`
    // range (raw `(ptr, len)` resolved by the caller via
    // `proof_layout.whir_base_evals_device_mut`). Eliminates the standalone
    // `claims_device` allocation and the post-D2H slab H2D-back loop.
    slab_claims_dst: (*mut E, usize),
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: BackwardKernels + Field + crate::ops::cub::device_reduce::Reduce + 'static,
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
        return Ok(());
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

    // `batch_reduce` writes its output through the slab's `whir.{kind}.evals`
    // range (B3). The slab is held alive by `_proof_slab` keepalive across
    // all base-layer reductions and the subsequent terminal D2H.
    let (slab_ptr, slab_len) = slab_claims_dst;
    assert_eq!(
        slab_len, columns_count,
        "slab whir.{label}.evals length must match trace_holder.columns_count",
    );
    // SAFETY: the slab destination memory outlives both the `batch_reduce`
    // kernel and the subsequent terminal D2H; `columns_count` is in-bounds.
    let claims_dst_slice = unsafe { DeviceSlice::from_raw_parts_mut(slab_ptr, columns_count) };
    batch_reduce(
        ReduceOperation::Sum,
        &mut reduction_temp,
        &block_partials_matrix,
        claims_dst_slice,
        stream,
    )?;
    reduction_range.end(stream)?;
    tracing_ranges.push(reduction_range);

    Ok(())
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
    // `batch_reduce` writes the per-column claims directly into the slab's
    // `whir.{setup,memory,witness}.evals` ranges. Cached-relation extras are
    // gathered from those slab ranges on device.
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    // Cached-relation extras are gathered from the slab-resident base evals
    // and committed into this final backward seed on-device.
    final_device_seed: &mut DeviceAllocation<u32>,
    context: &ProverContext,
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution<E>>
where
    E: Copy
        + BackwardKernels
        + FieldExtension<BF>
        + Field
        + crate::ops::cub::device_reduce::Reduce
        + 'static,
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

    // Route `batch_reduce`'s output of each base-layer column reduction
    // straight into the slab's `whir.{kind}.evals` range. Production does not
    // mirror those dense vectors here; cached relation extras are gathered
    // from the slab on device below, and final proof parsing reads the same
    // slab ranges after the terminal D2H.
    debug_assert_eq!(
        std::mem::size_of::<E>(),
        std::mem::size_of::<crate::primitives::field::E4>(),
        "base-layer slab routing requires E to be E4-sized",
    );
    let slab_claims_dst = |kind: WhirBaseLayerKind| -> (*mut E, usize) {
        let (ptr, len) = unsafe {
            proof_layout.whir_base_evals_device_mut(proof_slab.as_ptr() as *mut u8, kind)
        };
        (ptr as *mut E, len)
    };
    schedule_reduce_trace_holder_claims(
        "memory",
        memory_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Memory),
        &mut tracing_ranges,
        context,
    )?;
    schedule_reduce_trace_holder_claims(
        "witness",
        witness_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Witness),
        &mut tracing_ranges,
        context,
    )?;
    schedule_reduce_trace_holder_claims(
        "setup",
        setup_trace_holder,
        &eq_values,
        slab_claims_dst(WhirBaseLayerKind::Setup),
        &mut tracing_ranges,
        context,
    )?;

    let mut shared_state = Box::new(ScheduledBaseLayerClaimsState { result: None });
    let shared_state_handle = UnsafeMutAccessor::new(shared_state.as_mut());

    // Build the schedule-time SoA plan for the caching-relations extras. Only
    // `addresses` / `sources` metadata is kept — the production path gathers
    // extras values from the slab on device.
    let extras_plan = BaseLayerExtrasPlan::<E>::new(&layer_desc, initial_addresses, context);
    drop(layer_desc);
    let extras_addresses_accessor = crate::primitives::context::UnsafeAccessor::<[GKRAddress]>::new(
        extras_plan.addresses.as_ref(),
    );
    let extras_sources_accessor = crate::primitives::context::UnsafeAccessor::<[DenseSource]>::new(
        extras_plan.sources.as_ref(),
    );
    let shared_state_for_callback = shared_state_handle;
    let mut extras_values_device = None;
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

    // Build the metadata publication closure but defer its scheduling: the
    // caller places it at the front of WHIR start callbacks. Production path
    // gathers extras values from the slab on device; this closure only
    // publishes the address/source metadata for the terminal parser.
    let pending_aggregation: Box<dyn Fn() + Send + Sync + 'static> = Box::new(move || unsafe {
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
        _extras_values_device: extras_values_device,
        _extras_plan: extras_plan,
        extras_addresses_accessor,
        shared_state,
        pending_aggregation: Some(pending_aggregation),
    })
}

#[cfg(test)]
mod tests;
