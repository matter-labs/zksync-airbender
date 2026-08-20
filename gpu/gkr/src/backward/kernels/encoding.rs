use std::ffi::c_void;
use std::ptr::{null, null_mut};

use super::dim_reducing::{
    GKR_DIM_REDUCING_IO_PER_SLOT, GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, GKR_DIM_REDUCING_SLOTS,
};
use super::launchers::GkrEqSizes;
use crate::upstream::Field;
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::primitives::field::E4;

#[derive(Clone, Copy)]
pub(in crate::backward) struct FoldingArenaBinding {
    pub(crate) base: *const u8,
    pub(crate) log2_stride: u32,
}

impl FoldingArenaBinding {
    pub(in crate::backward) fn new(base: *const u8, log2_stride: u32) -> Self {
        assert!(!base.is_null());
        Self { base, log2_stride }
    }
}

pub(crate) const MAX_MAIN_LAYER_CLAIM_POINT_LEN: usize = super::GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;

cuda_struct_and_stub! {
    static ab_gkr_main_layer_claim_point: [E4; MAX_MAIN_LAYER_CLAIM_POINT_LEN];
}

pub(crate) fn get_main_layer_claim_point_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_main_layer_claim_point as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_main_layer_claim_point");
    ptr.cast()
}

// ---------------------------------------------------------------------------
// Compact dim-reducing descriptor types. Each source record carries two u16s:
// one for the source pointer/index and one for the cache pointer/index. Both
// halves resolve against the same per-launch `bases` / `log2_stride` tables.
// ---------------------------------------------------------------------------

/// Number of base pointers addressable by the 4-bit source pointer index.
pub(crate) const GKR_DIM_REDUCING_BASE_SLOTS: usize = 16;

/// One dim-reducing slot: `io[0..2]` inputs then `io[2..4]` outputs, plus the
/// batch-challenge table index for each output. Mirrors
/// `gkr_dim_reducing_slot` in `native/gkr/support/descriptors.cuh`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingSlot {
    pub(crate) io: [GpuGKRSourceRecord; GKR_DIM_REDUCING_IO_PER_SLOT],
    pub(crate) batch_exp: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
}

/// Per-launch pointer + stride tables.
/// `bases[ptr_idx]` is the base of slot `ptr_idx`'s allocation;
/// `log2_stride[ptr_idx]` is the per-poly stride exponent (decode:
/// `element_addr = bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx])`).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingTables {
    pub(crate) bases: [*const u8; GKR_DIM_REDUCING_BASE_SLOTS],
    pub(crate) log2_stride: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
}

impl Default for GpuGKRDimensionReducingTables {
    fn default() -> Self {
        Self {
            bases: [null(); GKR_DIM_REDUCING_BASE_SLOTS],
            log2_stride: [0; GKR_DIM_REDUCING_BASE_SLOTS],
        }
    }
}

// SAFETY: holds raw device pointers — safe to send across threads.
unsafe impl Send for GpuGKRDimensionReducingTables {}
unsafe impl Sync for GpuGKRDimensionReducingTables {}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct GpuGKRSourceRecord {
    pub(crate) src: u16,
    pub(crate) cache: u16,
}

impl GpuGKRSourceRecord {
    pub(crate) const fn source_only(src: u16) -> Self {
        Self { src, cache: 0 }
    }

    pub(crate) const fn new(src: u16, cache: u16) -> Self {
        Self { src, cache }
    }
}

/// Mirrors `gkr_dim_reducing_batch<E>`, shared by both dim-reducing round
/// kernels.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingBatch<E> {
    pub(crate) enabled_mask: u32,
    pub(crate) _reserved0: u32,
    pub(crate) eq_low: *const E,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) _eq_sizes_pad: u32,
    pub(crate) contributions: *mut E,
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) slots: [GpuGKRDimensionReducingSlot; GKR_DIM_REDUCING_SLOTS],
    pub(crate) _slots_pad: u32,
}

impl<E: Field> Default for GpuGKRDimensionReducingBatch<E> {
    fn default() -> Self {
        Self {
            enabled_mask: 0,
            _reserved0: 0,
            eq_low: null(),
            eq_sizes: GkrEqSizes::zeroed(),
            _eq_sizes_pad: 0,
            contributions: null_mut(),
            tables: GpuGKRDimensionReducingTables::default(),
            slots: [GpuGKRDimensionReducingSlot::default(); GKR_DIM_REDUCING_SLOTS],
            _slots_pad: 0,
        }
    }
}

/// `(first_access, ptr_idx, poly_idx)` packed into a u16 source descriptor.
/// `first_access` is bit 15 (cheapest single-bit test on the GPU);
/// `ptr_idx` is bits 14..11 (4 bits, 16 slots); `poly_idx` is bits 10..0
/// (11 bits, up to 2048 polys per slot).
#[inline]
pub(crate) const fn pack_source_u16(first_access: bool, ptr_idx: u8, poly_idx: u16) -> u16 {
    assert!(ptr_idx < 16, "pointer index exceeds 4-bit wire field");
    assert!(
        poly_idx < 2048,
        "polynomial index exceeds 11-bit wire field"
    );
    let fa = if first_access { 1u16 << 15 } else { 0 };
    fa | ((ptr_idx as u16) << 11) | poly_idx
}

/// Cache half of a dual source record. Bit 15 stays clear.
#[inline]
pub(crate) const fn pack_cache_u16(ptr_idx: u8, poly_idx: u16) -> u16 {
    assert!(ptr_idx < 16, "pointer index exceeds 4-bit wire field");
    assert!(
        poly_idx < 2048,
        "polynomial index exceeds 11-bit wire field"
    );
    ((ptr_idx as u16) << 11) | poly_idx
}
