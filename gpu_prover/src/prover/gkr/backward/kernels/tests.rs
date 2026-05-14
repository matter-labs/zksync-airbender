use std::collections::BTreeMap;
use std::mem::size_of;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{reduce, Reduce, ReduceOperation};
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::gkr_address_audit_helpers::{
    KERNEL_ARG_HARD_CEILING_BYTES, KERNEL_ARG_SOFT_TARGET_BYTES,
};
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};

impl ClaimBufferLayout {
    pub(crate) fn from_claims<E>(claims: &BTreeMap<GKRAddress, E>) -> Self {
        Self::from_addresses(claims.keys().copied().collect())
    }

    pub(crate) fn write_values_from_claims<E: Copy>(
        &self,
        claims: &BTreeMap<GKRAddress, E>,
        dst: &mut [E],
    ) {
        assert_eq!(
            dst.len(),
            self.len(),
            "claim buffer destination must match layout length"
        );
        for (idx, address) in self.addresses.iter().enumerate() {
            dst[idx] = claims
                .get(address)
                .copied()
                .unwrap_or_else(|| panic!("missing claim value for {address:?}"));
        }
    }
}

#[inline]
pub(crate) const fn unpack_source_u16(packed: u16) -> (bool, u8, u16) {
    let first_access = packed & (1 << 15) != 0;
    let ptr_idx = ((packed >> 11) & 0xF) as u8;
    let poly_idx = packed & 0x07FF;
    (first_access, ptr_idx, poly_idx)
}

impl<E: Copy + Field> GpuGKRMainLayerKernelPlan<E> {
    pub(crate) fn auxiliary_challenge_summary(&self) -> Option<E> {
        match self.auxiliary_challenge_source {
            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => Some(value),
            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => None,
        }
    }

    pub(crate) fn constraint_metadata_summary(&self) -> Option<(usize, usize, E)> {
        self.constraint_metadata_summary
    }
}

pub(crate) struct GpuGKRBackwardExecution<E: FieldExtension<BF> + Field> {
    pub(crate) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(crate) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

/// Allocate a device `DeviceAllocation<u32>` of length `STATE_SIZE` and H2D a host `Seed`
/// into it. Only test paths still need this bridge (the hot path threads the post-forward
/// device seed straight through). The staging buffer is filled inside a stream-ordered
/// callback (per the GPU scheduling contract — `HostAllocation` contents must not be touched
/// on the scheduling thread), so the caller-owned `Callbacks` must outlive stream execution.
pub(crate) fn h2d_seed_from_host(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    host_seed: &Seed,
) -> CudaResult<DeviceAllocation<u32>> {
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(crate::ops::blake2s::STATE_SIZE, AllocationPlacement::Top)?;
    let mut host_slot =
        unsafe { context.alloc_host_uninit_slice::<u32>(crate::ops::blake2s::STATE_SIZE) };
    let accessor = host_slot.get_mut_accessor();
    let seed_words = host_seed.0;
    callbacks.schedule(
        move || unsafe {
            accessor.get_mut().copy_from_slice(&seed_words);
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut d_seed, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(d_seed)
}

/// Allocate a device `DeviceAllocation<E>` of length `claim_point.len() + 1`, laid out as
/// `[claim_point || batching_challenge]` (matching the first backward layer's
/// `round_scratch.claim_point`), and H2D the host values into it. Only test paths still need
/// this bridge — the hot path threads the post-forward device squeeze buffer
/// (`d_evaluation_point_and_batching`) straight into the orchestrator. The staging buffer is
/// filled inside a stream-ordered callback; the caller-owned `Callbacks` must outlive stream
/// execution.
pub(crate) fn h2d_claim_point_and_batching_from_host<E: FieldExtension<BF> + Field + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    claim_point: &[E],
    batching_challenge: E,
) -> CudaResult<DeviceAllocation<E>> {
    let len = claim_point.len() + 1;
    let mut buf: DeviceAllocation<E> = context.alloc(len, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(len) };
    let accessor = host_slot.get_mut_accessor();
    let claim_point_owned: Vec<E> = claim_point.to_vec();
    callbacks.schedule(
        move || unsafe {
            let dst = accessor.get_mut();
            let (cp_dst, batching_dst) = dst.split_at_mut(claim_point_owned.len());
            cp_dst.copy_from_slice(&claim_point_owned);
            batching_dst[0] = batching_challenge;
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(buf)
}

/// Allocate a device claims buffer and upload values in the explicit order
/// defined by the returned `ClaimBufferLayout`. The staging buffer is filled
/// inside a stream-ordered callback; the caller-owned `Callbacks` must outlive
/// stream execution.
pub(crate) fn h2d_claims_from_host<E: FieldExtension<BF> + Field + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    claims: &BTreeMap<GKRAddress, E>,
) -> CudaResult<(DeviceAllocation<E>, ClaimBufferLayout)> {
    let layout = ClaimBufferLayout::from_claims(claims);
    let len = layout.len();
    let mut buf: DeviceAllocation<E> = context.alloc(len, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(len) };
    let accessor = host_slot.get_mut_accessor();
    let layout_for_callback = layout.clone();
    let claims_owned = claims.clone();
    callbacks.schedule(
        move || unsafe {
            layout_for_callback.write_values_from_claims(&claims_owned, accessor.get_mut());
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok((buf, layout))
}

/// Stage `[lookup_multiplicative, lookup_additive]` into a 2-element
/// device buffer, reading from `shared_state` inside a stream-ordered callback. Used
/// once per proof by the main-layer pipeline so per-layer `schedule_flat_eval_recipes`
/// can D2D these constants into its 3-scalar eval_recipes challenge buffer instead of
/// reading from host `workflow_state` on every layer. The caller-owned `Callbacks` must
/// outlive stream execution.
pub(crate) fn h2d_lookup_and_constraint_from_shared_state<E>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> CudaResult<DeviceAllocation<E>>
where
    E: FieldExtension<BF> + Field + 'static,
{
    let mut buf: DeviceAllocation<E> = context.alloc(2, AllocationPlacement::Top)?;
    let mut host_slot = unsafe { context.alloc_host_uninit_slice::<E>(2) };
    let accessor = host_slot.get_mut_accessor();
    callbacks.schedule(
        move || unsafe {
            let state = shared_state.get();
            let dst = accessor.get_mut();
            dst[0] = state.lookup_multiplicative_challenge;
            dst[1] = state.lookup_additive_challenge;
        },
        context.get_exec_stream(),
    )?;
    memory_copy_async(&mut buf, &host_slot, context.get_exec_stream())?;
    drop(host_slot);
    Ok(buf)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn populate_backward_workflow_state<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
    initial_output_layer_idx: usize,
    top_layer_claims: BTreeMap<GKRAddress, E>,
    evaluation_point: Vec<E>,
    seed: Seed,
    batching_challenge: E,
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) where
    E: FieldExtension<BF> + Field,
{
    let state = unsafe { shared_state.get_mut() };
    state.claims_for_layers =
        BTreeMap::from([(initial_output_layer_idx, top_layer_claims.clone())]);
    state.points_for_claims_at_layer =
        BTreeMap::from([(initial_output_layer_idx, evaluation_point.clone())]);
    state.current_claims = top_layer_claims;
    state.current_claim_point = evaluation_point;
    state.current_batching_challenge = batching_challenge;
    state.lookup_multiplicative_challenge = lookup_multiplicative_challenge;
    state.lookup_additive_challenge = lookup_additive_challenge;
    state.seed = seed;
}

pub(crate) fn take_backward_execution_from_shared_state<E>(
    shared_state: ScheduledBackwardWorkflowStateHandle<E>,
) -> GpuGKRBackwardExecution<E>
where
    E: FieldExtension<BF> + Field,
{
    let state = unsafe { shared_state.get_mut() };
    GpuGKRBackwardExecution {
        claims_for_layers: std::mem::take(&mut state.claims_for_layers),
        points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
        next_batching_challenge: state.current_batching_challenge,
        updated_seed: state.seed,
    }
}

pub(crate) fn apply_eq_and_reduce_accumulator<E>(
    eq_values: &DeviceAllocation<E>,
    accumulator: &mut DeviceAllocation<E>,
    reduction_output: &mut DeviceAllocation<E>,
    reduction_temp_storage: &mut DeviceAllocation<u8>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + Reduce,
    Mul: BinaryOp<E, E, E>,
{
    let stream = context.get_exec_stream();
    let eq_values = DeviceVectorChunk::new(eq_values, 0, acc_size);
    let reduction_temp = unsafe {
        DeviceSlice::from_raw_parts_mut(
            reduction_temp_storage.as_mut_ptr(),
            reduction_temp_storage.len(),
        )
    };

    {
        let mut low_half = DeviceVectorChunkMut::new(accumulator, 0, acc_size);
        mul_into_y(&eq_values, &mut low_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &low_half,
            &mut reduction_output[0],
            stream,
        )?;
    }

    {
        let mut high_half = DeviceVectorChunkMut::new(accumulator, acc_size, acc_size);
        mul_into_y(&eq_values, &mut high_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &high_half,
            &mut reduction_output[1],
            stream,
        )?;
    }

    Ok(())
}

#[test]
fn pack_source_u16_round_trips() {
    for first_access in [false, true] {
        for ptr_idx in 0u8..(GKR_DIM_REDUCING_BASE_SLOTS as u8) {
            for &poly_idx in &[0u16, 1, 2, 17, 255, 1024, 0x07FF] {
                let packed = pack_source_u16(first_access, ptr_idx, poly_idx);
                let (fa, p, q) = unpack_source_u16(packed);
                assert_eq!(fa, first_access);
                assert_eq!(p, ptr_idx);
                assert_eq!(q, poly_idx);
            }
        }
    }
}

#[test]
fn pack_source_u16_layout_bits() {
    // bit 15 = first_access, bits 14..11 = ptr_idx (4 bits, 16 slots),
    // bits 10..0 = poly_idx (11 bits, max 2048).
    assert_eq!(pack_source_u16(false, 0, 0), 0);
    assert_eq!(pack_source_u16(true, 0, 0), 0x8000);
    assert_eq!(pack_source_u16(false, 0xF, 0), 0x7800);
    assert_eq!(pack_source_u16(false, 0, 0x07FF), 0x07FF);
    assert_eq!(pack_source_u16(true, 0xF, 0x07FF), 0xFFFF);
}

#[test]
fn compact_descriptor_sizes_under_kernel_arg_ceiling() {
    let r0 = size_of::<GpuGKRDimensionReducingRound0BatchCompact<E4>>();
    let cont = size_of::<GpuGKRDimensionReducingContinuationBatchCompact<E4>>();
    // Both must fit comfortably under the soft 16 KB target (and well
    // under the 32 KB hard ceiling enforced by `cudaLaunchKernelExC`).
    assert!(
        r0 <= KERNEL_ARG_SOFT_TARGET_BYTES,
        "round0 compact = {r0} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
    );
    assert!(
        cont <= KERNEL_ARG_SOFT_TARGET_BYTES,
        "continuation compact = {cont} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
    );
    assert!(r0 < KERNEL_ARG_HARD_CEILING_BYTES);
    assert!(cont < KERNEL_ARG_HARD_CEILING_BYTES);
}

#[test]
fn compact_record_is_16_bytes() {
    // Audit's projected post-compaction footprint depends on this size.
    assert_eq!(
        size_of::<GpuGKRDimensionReducingBatchRecordCompact>(),
        16,
        "compact batch record size must remain 16 bytes"
    );
}
