use std::cell::UnsafeCell;
use std::collections::BTreeMap;

use era_cudart::slice::DeviceSlice;

use super::dim_reducing::GpuGKRDimensionReducingScheduledLayerExecution;
use super::main_layer::GpuGKRMainLayerScheduledLayerExecution;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, UnsafeAccessor, UnsafeMutAccessor};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};

/// Previous ceiling was 128; the unified circuit has 145 kernels in layer 0
/// (118 distinct reads, well within `FLAT_ROUND0_MAX_SOURCES = 1280`).
/// Raised to 256 to give headroom for future circuits.
///
/// MUST stay in lockstep with the native mirror in
/// `native/prover/gkr/support/descriptors.cuh` (`GKR_BACKWARD_MAX_KERNELS_PER_LAYER`).
/// Unlike the dim-reducing caps, this one sizes no shared `extern "C"` array (it
/// is only a `<=` capacity assert on both sides), so nothing structural catches
/// drift — the `gkr_backward_max_kernels_lockstep` test below pins the value to
/// force a matching native edit.
pub(crate) const GKR_BACKWARD_MAX_KERNELS_PER_LAYER: usize = 256;
/// Supported GKR trace-length ceiling. Backward folding uses one challenge per
/// trace dimension, so a `2^24` trace has at most 24 folding steps.
pub(crate) const GKR_BACKWARD_MAX_TRACE_LEN_LOG2: usize = 24;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClaimBufferLayout {
    pub(crate) addresses: Vec<GKRAddress>,
    pub(crate) index_by_address: BTreeMap<GKRAddress, u32>,
}

impl ClaimBufferLayout {
    pub(crate) fn from_addresses(addresses: Vec<GKRAddress>) -> Self {
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

    pub(crate) fn len(&self) -> usize {
        self.addresses.len()
    }

    pub(crate) fn claim_idx(&self, address: &GKRAddress) -> u32 {
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

#[allow(dead_code)]
pub(crate) struct ScheduledChallengeBuffer<E> {
    pub(crate) device: UnsafeAccessor<SharedChallengeDevice<E>>,
    pub(crate) offset: usize,
    pub(crate) len: usize,
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

    pub(crate) fn device_accessor(&self) -> UnsafeAccessor<SharedChallengeDevice<E>> {
        UnsafeAccessor::new(
            self.device
                .as_deref()
                .expect("challenge storage device already released"),
        )
    }

    /// Release the per-layer batch-challenge device buffer. Its last scheduled
    /// use is this main layer's backward sumcheck (the `device_accessor`
    /// pointer is only dereferenced by those enqueued kernels), so the
    /// reservation frees stream-ordered at prove-end like the other backward
    /// handoff buffers.
    pub(crate) fn release_device(&mut self) {
        self.device = None;
    }
}

pub(crate) struct DeviceClaimPointAndBatching<E> {
    ptr: usize,
    len: usize,
    #[allow(dead_code)]
    owner: Option<DeviceAllocation<E>>,
}

impl<E> DeviceClaimPointAndBatching<E> {
    pub(crate) fn from_allocation(allocation: DeviceAllocation<E>) -> Self {
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

    #[cfg(test)]
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
/// consumes them. (Type alias documenting intent at the field site.)
pub(crate) type ScheduledDimensionReducingFinalReadback = Callbacks<'static>;

pub(crate) type ScheduledBackwardWorkflowStateHandle<E> =
    UnsafeMutAccessor<ScheduledBackwardWorkflowState<E>>;

#[allow(dead_code)]
pub(crate) struct ScheduledBackwardWorkflowState<E: FieldExtension<BF> + Field> {
    pub(crate) claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    pub(crate) points_for_claims_at_layer: BTreeMap<usize, Vec<E>>,
    pub(crate) current_claims: BTreeMap<GKRAddress, E>,
    pub(crate) current_claim_point: Vec<E>,
    pub(crate) current_batching_challenge: E,
    pub(crate) lookup_multiplicative_challenge: E,
    pub(crate) lookup_additive_challenge: E,
    pub(crate) seed: Seed,
}

pub(crate) struct GpuGKRBackwardScheduledExecution<B, E: FieldExtension<BF> + Field> {
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

pub(crate) fn make_deferred_backward_workflow_state<E>() -> Box<ScheduledBackwardWorkflowState<E>>
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
        assert_eq!(GKR_BACKWARD_MAX_KERNELS_PER_LAYER, 256);
    }
}
