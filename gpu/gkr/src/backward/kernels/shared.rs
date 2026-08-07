use std::collections::BTreeMap;

use era_cudart::slice::DeviceSlice;

use super::dim_reducing::GpuGKRDimensionReducingScheduledLayerExecution;
use super::main_layer::GpuGKRMainLayerScheduledLayerExecution;
use crate::upstream::GKRAddress;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::E4;

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

pub(crate) struct DeviceClaimPointAndBatching {
    ptr: usize,
    len: usize,
    #[allow(dead_code)]
    owner: Option<DeviceAllocation<E4>>,
}

impl DeviceClaimPointAndBatching {
    pub(crate) fn from_allocation(allocation: DeviceAllocation<E4>) -> Self {
        let ptr = allocation.as_ptr() as usize;
        let len = allocation.len();
        Self {
            ptr,
            len,
            owner: Some(allocation),
        }
    }

    pub(crate) unsafe fn from_raw_symbol_parts(ptr: *mut E4, len: usize) -> Self {
        Self {
            ptr: ptr as usize,
            len,
            owner: None,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn as_ptr(&self) -> *const E4 {
        self.ptr as *const E4
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut E4 {
        self.ptr as *mut E4
    }
    pub(crate) fn slice(&self, offset: usize, len: usize) -> &DeviceSlice<E4> {
        assert!(offset <= self.len && len <= self.len - offset);
        unsafe { DeviceSlice::from_raw_parts(self.as_ptr().add(offset), len) }
    }

    pub(crate) fn slice_mut(&mut self, offset: usize, len: usize) -> &mut DeviceSlice<E4> {
        assert!(offset <= self.len && len <= self.len - offset);
        unsafe { DeviceSlice::from_raw_parts_mut(self.as_mut_ptr().add(offset), len) }
    }
}

pub struct GpuGKRBackwardScheduledExecution {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    pub(crate) dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution>,
    #[allow(dead_code)]
    pub(crate) main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution>,
    pub(crate) final_device_seed: Option<DeviceAllocation<u32>>,
    pub(crate) final_device_claim_point_and_batching: Option<DeviceClaimPointAndBatching>,
    pub(crate) final_claim_layout: Option<ClaimBufferLayout>,
}
