use std::collections::{BTreeMap, BTreeSet};

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::backward::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    launch_trace_holder_block_partials_eq_inline, launch_trace_holder_column_sums, make_eq_sizes,
    GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK,
};
use crate::proof_layout::{ProofLayout, WhirBaseLayerKind};
use crate::upstream::{GKRAddress, GKRLayerDescription, VirtualSetupPoly};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeAccessor};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;

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
pub(crate) struct GpuGKRBaseLayerTailOutput {
    pub(crate) extra_evaluations_addresses: UnsafeAccessor<[GKRAddress]>,
    extra_evaluations_sources: UnsafeAccessor<[DenseSource]>,
}

pub struct ScheduledBaseLayerClaimsState {
    result: Option<GpuGKRBaseLayerTailOutput>,
}

pub fn clone_base_layer_extra_evaluations_from_slab(
    shared_state: UnsafeAccessor<ScheduledBaseLayerClaimsState>,
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

    unsafe fn device_ptr(
        self,
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
    ) -> *const E4 {
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
        base.add(offset) as *const E4
    }
}

/// Schedule-time-known SoA description of the layer-0 caching-relations extras:
/// the addresses whose dependency claims must be filled from per-column dense
/// flats and the matching dense source for each. Shape is intentionally
/// GPU-friendly (parallel arrays, schedule-time-fixed length) so this can move
/// off the host as the eventual GPU port lands.
struct BaseLayerExtrasPlan {
    addresses: Box<[GKRAddress]>,
    sources: Box<[DenseSource]>,
}

impl BaseLayerExtrasPlan {
    fn new(layer_desc: &GKRLayerDescription, initial_addresses: &[GKRAddress]) -> Self {
        let mut already_present: BTreeSet<GKRAddress> = initial_addresses.iter().copied().collect();
        already_present.extend(VIRTUAL_SETUP_ADDRESSES.iter().copied());
        let mut missing: BTreeSet<GKRAddress> = BTreeSet::new();
        for (cached_addr, relation) in layer_desc.cached_relations.iter() {
            assert!(
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
        Self { addresses, sources }
    }
}

pub struct GpuGKRBaseLayerClaimsScheduledExecution {
    _tracing_ranges: Vec<Range>,
    // Device gather of cached-relation extras. It is committed into the final
    // backward seed on-device, so it must live until stream work ends.
    _extras_values_device: Option<DeviceAllocation<E4>>,
    // Schedule-time-built plan for layer-0 caching-relations extras. The plan
    // owns the metadata; addresses/sources accessors point into it.
    _extras_plan: BaseLayerExtrasPlan,
    shared_state: Box<ScheduledBaseLayerClaimsState>,
}

impl GpuGKRBaseLayerClaimsScheduledExecution {
    pub fn shared_state_handle(&self) -> UnsafeAccessor<ScheduledBaseLayerClaimsState> {
        UnsafeAccessor::new(self.shared_state.as_ref())
    }

    /// Release the device gather of cached-relation extras. It has been
    /// committed into the final backward seed on-device by prove-end, so the
    /// reservation frees stream-ordered. The schedule-time host metadata (the
    /// extras plan + addresses accessor + the `result` sink read by the
    /// terminal callback) stays.
    pub fn release_device_buffers(&mut self) {
        self._extras_values_device = None;
    }
}

fn schedule_reduce_trace_holder_claims(
    label: &str,
    trace_holder: &TraceHolder<BF>,
    eq_low: &DeviceSlice<E4>,
    eq_sizes: GkrEqSizes,
    // The column-sums kernel writes straight into the slab's
    // `whir.{kind}.evals` range (raw `(ptr, len)` resolved by the caller via
    // `proof_layout.whir_base_evals_device_mut`).
    slab_claims_dst: (*mut E4, usize),
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = 1usize << trace_holder.log_domain_size;
    assert_eq!(eq_low.len(), GKR_EQ_GROUP_TABLE_LEN);
    assert!(trace_len <= u32::MAX as usize);
    assert_eq!(
        trace_len % 4,
        0,
        "base-layer claims require trace lengths divisible by 4"
    );
    let columns_count = trace_holder.columns_count;
    assert!(columns_count <= u32::MAX as usize);
    if columns_count == 0 {
        return Ok(());
    }

    // 2 blocks/SM (the register-file cap): 1 block/SM leaves the inline-eq
    // latency uncovered.
    let blocks_count = 2 * context.get_device_properties().sm_count;
    assert!(blocks_count > 0, "device must expose at least one SM");
    assert!(blocks_count <= u32::MAX as usize);

    let mut block_partials =
        context.alloc(columns_count * blocks_count, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    let reduction_range = Range::new(format!("gkr.base_layer_claims.reduce.{label}"))?;
    reduction_range.start(stream)?;
    let raw_values = trace_holder.get_hypercube_evals();
    for column_start in (0..columns_count).step_by(GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK) {
        let chunk_cols =
            (columns_count - column_start).min(GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK);
        launch_trace_holder_block_partials_eq_inline(
            raw_values.as_ptr(),
            eq_low.as_ptr(),
            eq_sizes,
            block_partials.as_mut_ptr(),
            trace_len,
            column_start,
            chunk_cols,
            blocks_count,
            context,
        )?;
    }

    // The slab destination is held alive by the `_proof_slab` keepalive across
    // all base-layer reductions and the subsequent terminal D2H.
    let (slab_ptr, slab_len) = slab_claims_dst;
    assert_eq!(
        slab_len, columns_count,
        "slab whir.{label}.evals length must match trace_holder.columns_count",
    );
    launch_trace_holder_column_sums(
        block_partials.as_ptr(),
        slab_ptr,
        columns_count,
        blocks_count,
        context,
    )?;
    reduction_range.end(stream)?;
    tracing_ranges.push(reduction_range);

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn schedule_prepare_base_layer_claims_with_sources(
    layer_desc: GKRLayerDescription,
    claim_point_device: &DeviceSlice<E4>,
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
) -> CudaResult<GpuGKRBaseLayerClaimsScheduledExecution> {
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

    // Overwriting the shared `ab_gkr_eq_high` `__constant__` slabs is safe:
    // backward's last read of them precedes this schedule.
    let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
    launch_build_eq_high_and_low_groups_from_point(
        claim_point_device.as_ptr(),
        0,
        claim_point_len,
        get_eq_high_constant_device_ptr(),
        eq_low.as_mut_ptr(),
        context,
    )?;
    let eq_sizes = make_eq_sizes(claim_point_len);

    // Route each column reduction's output straight into the slab's
    // `whir.{kind}.evals` range. Production does not mirror those dense
    // vectors here; cached relation extras are gathered from the slab on
    // device below, and final proof parsing reads the same slab ranges after
    // the terminal D2H.
    let slab_claims_dst = |kind: WhirBaseLayerKind| -> (*mut E4, usize) {
        let (ptr, len) = unsafe {
            proof_layout.whir_base_evals_device_mut(proof_slab.as_ptr() as *mut u8, kind)
        };
        (ptr as *mut E4, len)
    };
    schedule_reduce_trace_holder_claims(
        "memory",
        memory_trace_holder,
        &eq_low,
        eq_sizes,
        slab_claims_dst(WhirBaseLayerKind::Memory),
        &mut tracing_ranges,
        context,
    )?;
    schedule_reduce_trace_holder_claims(
        "witness",
        witness_trace_holder,
        &eq_low,
        eq_sizes,
        slab_claims_dst(WhirBaseLayerKind::Witness),
        &mut tracing_ranges,
        context,
    )?;
    schedule_reduce_trace_holder_claims(
        "setup",
        setup_trace_holder,
        &eq_low,
        eq_sizes,
        slab_claims_dst(WhirBaseLayerKind::Setup),
        &mut tracing_ranges,
        context,
    )?;

    let extras_plan = BaseLayerExtrasPlan::new(&layer_desc, initial_addresses);
    drop(layer_desc);
    let extras_addresses_accessor =
        gpu_core::primitives::context::UnsafeAccessor::<[GKRAddress]>::new(
            extras_plan.addresses.as_ref(),
        );
    let extras_sources_accessor =
        gpu_core::primitives::context::UnsafeAccessor::<[DenseSource]>::new(
            extras_plan.sources.as_ref(),
        );
    let shared_state = Box::new(ScheduledBaseLayerClaimsState {
        result: Some(GpuGKRBaseLayerTailOutput {
            extra_evaluations_addresses: extras_addresses_accessor,
            extra_evaluations_sources: extras_sources_accessor,
        }),
    });
    let mut extras_values_device = None;
    if !extras_plan.sources.is_empty() {
        let src_ptrs: Vec<u64> = extras_plan
            .sources
            .iter()
            .copied()
            .map(|source| unsafe { source.device_ptr(proof_slab, proof_layout) as u64 })
            .collect();
        let mut d_values =
            context.alloc::<E4>(extras_plan.sources.len(), AllocationPlacement::BestFit)?;
        gpu_hash::blake2s::gather_e_addresses(&src_ptrs, &mut d_values, stream)?;
        let d_values_u32 = unsafe { d_values.transmute::<u32>() };
        gpu_hash::blake2s::transcript_commit(final_device_seed, d_values_u32, stream)?;
        extras_values_device = Some(d_values);
    }

    schedule_range.end(stream)?;
    tracing_ranges.push(schedule_range);

    Ok(GpuGKRBaseLayerClaimsScheduledExecution {
        _tracing_ranges: tracing_ranges,
        _extras_values_device: extras_values_device,
        _extras_plan: extras_plan,
        shared_state,
    })
}
