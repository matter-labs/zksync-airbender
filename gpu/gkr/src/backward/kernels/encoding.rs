use std::ffi::c_void;
use std::ptr::{null, null_mut};

use super::dim_reducing::GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER;
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

pub(crate) const GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD: usize = 2;
pub(crate) const GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD: usize = 2;
pub(crate) const GKR_DIM_REDUCING_INLINE_RECORD_CAP: usize = GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER
    * (GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD + GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD);

/// Number of base pointers addressable by the 4-bit source pointer index.
pub(crate) const GKR_DIM_REDUCING_BASE_SLOTS: usize = 16;

/// `(offset, count)` over the `inline_payload[GpuGKRSourceRecord]` array.
/// 4 B per range record.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct PayloadRange16 {
    pub(crate) offset: u16,
    pub(crate) count: u16,
}

/// One dim-reducing record (kernel-batch entry).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct GpuGKRDimensionReducingBatchRecordCompact {
    pub(crate) kind: u32,
    pub(crate) inputs: PayloadRange16,
    pub(crate) outputs: PayloadRange16,
    pub(crate) batch_challenge_offset: u16,
    pub(crate) _reserved: u16,
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

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound0BatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) eq_low: *const E,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) _eq_sizes_pad: u32,
    pub(crate) contributions: *mut E,
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_RECORD_CAP],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound0BatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            eq_low: null(),
            eq_sizes: GkrEqSizes::zeroed(),
            _eq_sizes_pad: 0,
            contributions: null_mut(),
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_RECORD_CAP],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingContinuationBatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) eq_low: *const E,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) _eq_sizes_pad: u32,
    pub(crate) contributions: *mut E,
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_RECORD_CAP],
}

impl<E: Field> Default for GpuGKRDimensionReducingContinuationBatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            eq_low: null(),
            eq_sizes: GkrEqSizes::zeroed(),
            _eq_sizes_pad: 0,
            contributions: null_mut(),
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_RECORD_CAP],
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
