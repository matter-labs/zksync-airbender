use std::ptr::null;

use crate::upstream::{GKRAddress, VirtualSetupPoly};

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum GpuBaseFieldSourceKind {
    Empty = 0,
    Real = 1,
    VirtualRangeCheck16Bits = 2,
    VirtualRangeCheckTimestamp = 3,
    VirtualInitsAndTeardownsLow = 4,
    VirtualInitsAndTeardownsHigh = 5,
}

impl Clone for GpuBaseFieldSourceKind {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for GpuBaseFieldSourceKind {}

impl Default for GpuBaseFieldSourceKind {
    fn default() -> Self {
        Self::Empty
    }
}

impl GpuBaseFieldSourceKind {
    pub(crate) const fn from_virtual_setup(poly: VirtualSetupPoly) -> Self {
        match poly {
            VirtualSetupPoly::RangeCheck16Bits => Self::VirtualRangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp => Self::VirtualRangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow => Self::VirtualInitsAndTeardownsLow,
            VirtualSetupPoly::InitsAndTeardownsHigh => Self::VirtualInitsAndTeardownsHigh,
        }
    }

    pub(crate) const fn from_address(address: GKRAddress) -> Option<Self> {
        match address {
            GKRAddress::VirtualSetup(poly) => Some(Self::from_virtual_setup(poly)),
            _ => None,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySource<B> {
    pub(crate) start: *const B,
    pub(crate) next_layer_size: usize,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B> Clone for GpuBaseFieldPolySource<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B> Copy for GpuBaseFieldPolySource<B> {}

// SAFETY: contains only a device pointer and a size — safe to send across threads.
unsafe impl<B> Send for GpuBaseFieldPolySource<B> {}
unsafe impl<B> Sync for GpuBaseFieldPolySource<B> {}

impl<B> GpuBaseFieldPolySource<B> {
    pub(crate) fn empty() -> Self {
        Self {
            start: null(),
            next_layer_size: 0,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

// These descriptors live in preallocated host/device buffers that are owned by the scheduler.
// Dynamic transcript data is staged separately in tiny per-round challenge buffers.
// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
    pub(crate) _marker: core::marker::PhantomData<E>,
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}

// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuExtensionFieldPolyInitialSource<E> {
    pub(crate) start: *const E,
    pub(crate) next_layer_size: usize,
}

impl<E> Clone for GpuExtensionFieldPolyInitialSource<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Copy for GpuExtensionFieldPolyInitialSource<E> {}

// SAFETY: contains only a device pointer and a size — safe to send across threads.
unsafe impl<E> Send for GpuExtensionFieldPolyInitialSource<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyInitialSource<E> {}

impl<E> GpuExtensionFieldPolyInitialSource<E> {
    pub(crate) fn empty() -> Self {
        Self {
            start: null(),
            next_layer_size: 0,
        }
    }
}

// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
}

impl<E: Copy> Clone for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Copy> Copy for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<E> Send for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound0LaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyInitialSource<E>>,
    pub(crate) base_field_outputs: Vec<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_outputs: Vec<GpuExtensionFieldPolyInitialSource<E>>,
}

impl<B, E> Default for GpuSumcheckRound0LaunchDescriptors<B, E> {
    fn default() -> Self {
        Self {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
            base_field_outputs: Vec::new(),
            extension_field_outputs: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E> Clone for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E> Copy for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}

unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}

impl<B, E> GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    pub(crate) fn empty() -> Self {
        Self {
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_input_start: null(),
            this_layer_cache_start: null::<E>().cast_mut(),
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

#[derive(Debug)]
pub(crate) struct GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E> Clone for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E> Copy for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}

unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}

impl<B, E> GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    pub(crate) fn empty() -> Self {
        Self {
            base_input_start: null(),
            this_layer_cache_start: null::<E>().cast_mut(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

#[derive(Debug)]
pub(crate) struct GpuExtensionFieldPolyContinuingSourcePlan<E> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
}

impl<E> Clone for GpuExtensionFieldPolyContinuingSourcePlan<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Copy for GpuExtensionFieldPolyContinuingSourcePlan<E> {}

unsafe impl<E> Send for GpuExtensionFieldPolyContinuingSourcePlan<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyContinuingSourcePlan<E> {}

impl<E> GpuExtensionFieldPolyContinuingSourcePlan<E> {
    pub(crate) fn empty() -> Self {
        Self {
            previous_layer_start: null(),
            this_layer_start: null::<E>().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: false,
        }
    }
}
