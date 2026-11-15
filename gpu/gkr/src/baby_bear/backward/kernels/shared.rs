use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::{context::DeviceAllocation, device_tracing::Range, field::E4};

use crate::{
    baby_bear::backward::kernels::{
        dim_reducing::GpuGKRDimensionReducingScheduledLayerExecution,
        main_layer::GpuGKRMainLayerScheduledLayerExecution,
    },
    backward::kernels::shared::*,
};

pub(crate) struct DeviceClaimPointAndBatching {
    ptr: usize,
    len: usize,
    #[allow(dead_code)] // Owns the allocation when the pointer is not a borrowed symbol.
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
    pub(crate) dimension_reducing_layers: Vec<GpuGKRDimensionReducingScheduledLayerExecution>,
    pub(crate) main_layers: Vec<GpuGKRMainLayerScheduledLayerExecution>,
    pub(crate) final_device_seed: Option<DeviceAllocation<u32>>,
    pub(crate) final_device_claim_point_and_batching: Option<DeviceClaimPointAndBatching>,
    pub(crate) final_claim_layout: Option<ClaimBufferLayout>,
}
