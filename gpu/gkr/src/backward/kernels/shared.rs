use std::cell::UnsafeCell;
use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::dim_reducing::GpuGKRDimensionReducingScheduledLayerExecution;
use super::main_layer::GpuGKRMainLayerScheduledLayerExecution;
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::BF;
use gpu_prover_context::ProverContext;

/// Sized for the blake2_with_compression delegation, whose largest
/// main layer fuses 547 kernels. 1024 gives ~2x headroom and stays
/// under the dim-reducing descriptor-size projection ceiling (~1712 before the
/// projected struct would exceed the 32 KB kernel-arg limit; see
/// `gkr_address_audit_helpers::compaction_sizes`).
///
/// MUST stay in lockstep with the native mirror in
/// `native/prover/gkr/support/descriptors.cuh` (`GKR_BACKWARD_MAX_KERNELS_PER_LAYER`).
/// Unlike the dim-reducing caps, this one sizes no shared `extern "C"` array (it
/// is only a `<=` capacity assert on both sides), so nothing structural catches
/// drift — the `gkr_backward_max_kernels_lockstep` test below pins the value to
/// force a matching native edit.
pub(crate) const GKR_BACKWARD_MAX_KERNELS_PER_LAYER: usize = 1024;
/// Supported GKR trace-length ceiling. Backward folding uses one challenge per
/// trace dimension, so a `2^24` trace has at most 24 folding steps.
pub(crate) const GKR_BACKWARD_MAX_TRACE_LEN_LOG2: usize = 24;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimBufferLayout {
    pub(crate) addresses: Vec<GKRAddress>,
    pub(crate) index_by_address: BTreeMap<GKRAddress, u32>,
}

impl ClaimBufferLayout {
    pub fn from_addresses(addresses: Vec<GKRAddress>) -> Self {
        assert!(
            !addresses.is_empty(),
            "claim buffer layout must contain at least one address"
        );
        assert!(
            addresses.len() <= u32::MAX as usize,
            "claim buffer layout exceeds u32 indexing"
        );
        let mut index_by_address = BTreeMap::new();
        for (idx, address) in addresses.iter().copied().enumerate() {
            let prev = index_by_address.insert(address, idx as u32);
            assert!(
                prev.is_none(),
                "duplicate claim address in claim buffer layout: {address:?}"
            );
        }
        Self {
            addresses,
            index_by_address,
        }
    }

    pub fn len(&self) -> usize {
        self.addresses.len()
    }

    pub fn claim_idx(&self, address: &GKRAddress) -> u32 {
        self.index_by_address
            .get(address)
            .copied()
            .unwrap_or_else(|| panic!("missing claim address in layout: {address:?}"))
    }
}

pub(crate) struct SharedChallengeDevice<E> {
    pub(crate) device: UnsafeCell<DeviceAllocation<E>>,
}

// SAFETY: uploads and kernel launches are enqueued from the host in stream order.
// SharedChallengeDevice only exposes raw pointers or temporary slice views for those enqueues.
unsafe impl<E: Send> Send for SharedChallengeDevice<E> {}
// SAFETY: the wrapped device allocation lives for the duration of all queued work and is only
// accessed through explicit pointer/slice helpers.
unsafe impl<E: Sync> Sync for SharedChallengeDevice<E> {}

impl<E> SharedChallengeDevice<E> {
    pub(crate) fn new(device: DeviceAllocation<E>) -> Self {
        Self {
            device: UnsafeCell::new(device),
        }
    }

    pub(crate) unsafe fn slice_mut(&mut self, offset: usize, len: usize) -> &mut DeviceSlice<E> {
        // SAFETY: callers guarantee the requested range is within bounds and use
        // this temporary mutable view only to enqueue stream-ordered device work.
        &mut (&mut *self.device.get())[offset..offset + len]
    }
}

pub(crate) struct ScheduledChallengeStorage<E> {
    #[allow(dead_code)] // keepalive: callbacks must outlive the scheduled stream ops.
    pub(crate) callbacks: Callbacks<'static>,
    pub(crate) device: Option<Box<SharedChallengeDevice<E>>>,
}

impl<E> ScheduledChallengeStorage<E> {
    pub(crate) fn new(device: DeviceAllocation<E>) -> Self {
        Self {
            callbacks: Callbacks::new(),
            device: Some(Box::new(SharedChallengeDevice::new(device))),
        }
    }

    /// Release the per-layer batch-challenge device buffer. Its last scheduled
    /// use is this main layer's backward sumcheck, so the reservation frees
    /// stream-ordered at prove-end like the other backward handoff buffers.
    pub(crate) fn release_device(&mut self) {
        self.device = None;
    }
}

#[doc(hidden)]
pub struct DeviceClaimPointAndBatching<E> {
    ptr: usize,
    len: usize,
    #[allow(dead_code)]
    owner: Option<DeviceAllocation<E>>,
}

impl<E> DeviceClaimPointAndBatching<E> {
    pub fn from_allocation(allocation: DeviceAllocation<E>) -> Self {
        let ptr = allocation.as_ptr() as usize;
        let len = allocation.len();
        Self {
            ptr,
            len,
            owner: Some(allocation),
        }
    }

    pub(crate) unsafe fn from_raw_symbol_parts(ptr: *mut E, len: usize) -> Self {
        Self {
            ptr: ptr as usize,
            len,
            owner: None,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn as_ptr(&self) -> *const E {
        self.ptr as *const E
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut E {
        self.ptr as *mut E
    }
    pub(crate) fn as_slice(&self) -> &DeviceSlice<E> {
        unsafe { DeviceSlice::from_raw_parts(self.as_ptr(), self.len) }
    }

    pub(crate) unsafe fn slice(&self, offset: usize, len: usize) -> &DeviceSlice<E> {
        assert!(offset <= self.len && len <= self.len - offset);
        DeviceSlice::from_raw_parts(self.as_ptr().add(offset), len)
    }

    pub(crate) unsafe fn slice_mut(&mut self, offset: usize, len: usize) -> &mut DeviceSlice<E> {
        assert!(offset <= self.len && len <= self.len - offset);
        DeviceSlice::from_raw_parts_mut(self.as_mut_ptr().add(offset), len)
    }
}

/// SCHEDULING keepalive — keeps host callbacks alive until the stream
/// consumes them.
pub(crate) type ScheduledDimensionReducingFinalReadback = Callbacks<'static>;

pub type ScheduledBackwardWorkflowStateHandle<E> =
    UnsafeMutAccessor<ScheduledBackwardWorkflowState<E>>;

#[allow(dead_code)]
pub struct ScheduledBackwardWorkflowState<E: FieldExtension<BF> + Field> {
    pub(crate) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(crate) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(crate) current_claims: BTreeMap<GKRAddress, E>,
    pub(crate) current_claim_point: Vec<E>,
    pub(crate) current_batching_challenge: E,
    pub(crate) lookup_multiplicative_challenge: E,
    pub(crate) lookup_additive_challenge: E,
    pub(crate) seed: Seed,
}

pub struct GpuGKRBackwardScheduledExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(crate) dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution<B, E>>,
    #[allow(dead_code)]
    pub(crate) main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution<E>>,
    pub(crate) shared_state: Box<ScheduledBackwardWorkflowState<E>>,
    #[allow(dead_code)]
    // Keeps test-path initial-staging callbacks alive until the stream consumes them.
    pub(crate) initial_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(crate) external_challenges_device_keepalive: Option<DeviceAllocation<E>>,
    pub(crate) final_device_seed: Option<DeviceAllocation<u32>>,
    pub(crate) final_device_claim_point_and_batching: Option<DeviceClaimPointAndBatching<E>>,
    pub(crate) final_claim_layout: Option<ClaimBufferLayout>,
}

impl<E> ScheduledBackwardWorkflowState<E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn deferred() -> Self {
        Self {
            claims_for_layers: BTreeMap::new(),
            points_for_claims_at_layer: BTreeMap::new(),
            current_claims: BTreeMap::new(),
            current_claim_point: Vec::new(),
            current_batching_challenge: E::ZERO,
            lookup_multiplicative_challenge: E::ZERO,
            lookup_additive_challenge: E::ZERO,
            seed: Seed::default(),
        }
    }
}

pub fn make_deferred_backward_workflow_state<E>() -> Box<ScheduledBackwardWorkflowState<E>>
where
    E: FieldExtension<BF> + Field,
{
    Box::new(ScheduledBackwardWorkflowState::deferred())
}

#[cfg(test)]
mod cap_tests {
    use super::GKR_BACKWARD_MAX_KERNELS_PER_LAYER;

    // Lockstep guard, mirroring `gkr_dim_reducing_caps_lockstep`: this value is
    // mirrored verbatim into native/prover/gkr/support/descriptors.cuh:51. It
    // sizes no shared array, so there is no ABI tie to catch drift — if you
    // change one side you MUST change the other; this test fails loudly to force it.
    #[test]
    fn gkr_backward_max_kernels_lockstep() {
        assert_eq!(GKR_BACKWARD_MAX_KERNELS_PER_LAYER, 1024);
    }
}

// ---- Relocated from `#[cfg(test)] mod tests` (cluster A/gap): production-
// shaped backward-workflow test-driver helpers the apex e2e suite reaches
// across the crate boundary. `#[doc(hidden)] pub` per the split's
// test-reference policy.
impl ClaimBufferLayout {
    #[doc(hidden)]
    pub fn from_claims<E>(claims: &BTreeMap<GKRAddress, E>) -> Self {
        Self::from_addresses(claims.keys().copied().collect())
    }

    #[doc(hidden)]
    pub fn write_values_from_claims<E: Copy>(
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

#[doc(hidden)]
pub struct GpuGKRBackwardExecution<E: FieldExtension<BF> + Field> {
    pub claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub next_batching_challenge: E,
    pub updated_seed: Seed,
}

/// Allocate a device `DeviceAllocation<u32>` of length `STATE_SIZE` and H2D a host `Seed`
/// into it. Only test paths still need this bridge (the hot path threads the post-forward
/// device seed straight through). The staging buffer is filled inside a stream-ordered
/// callback (per the GPU scheduling contract — `HostAllocation` contents must not be touched
/// on the scheduling thread), so the caller-owned `Callbacks` must outlive stream execution.
#[doc(hidden)]
pub fn h2d_seed_from_host(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    host_seed: &Seed,
) -> CudaResult<DeviceAllocation<u32>> {
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(gpu_hash::blake2s::STATE_SIZE, AllocationPlacement::Top)?;
    let mut host_slot =
        unsafe { context.alloc_host_uninit_slice::<u32>(gpu_hash::blake2s::STATE_SIZE) };
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
#[doc(hidden)]
pub fn h2d_claim_point_and_batching_from_host<E: FieldExtension<BF> + Field + 'static>(
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
#[doc(hidden)]
pub fn h2d_claims_from_host<E: FieldExtension<BF> + Field + 'static>(
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
#[doc(hidden)]
pub fn h2d_lookup_and_constraint_from_shared_state<E>(
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
#[doc(hidden)]
pub fn populate_backward_workflow_state<E>(
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

#[doc(hidden)]
pub fn take_backward_execution_from_shared_state<E>(
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
