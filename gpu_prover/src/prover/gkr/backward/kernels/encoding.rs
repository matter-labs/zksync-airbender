use std::ptr::{null, null_mut};

use super::dim_reducing::GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER;
use crate::upstream::Field;

// ---------------------------------------------------------------------------
// Compact dim-reducing descriptor types. Each source record carries two u16s:
// one for the source pointer/index and one for the cache pointer/index. Both
// halves resolve against the same per-launch `bases` / `log2_stride` tables.
// ---------------------------------------------------------------------------

/// Pessimistic upper bound on the per-launch u16 source list. Anchored to
/// `FLAT_ROUND0_MAX_SOURCES = 1280` (see `gkr_address_audit.rs`).
pub(crate) const GKR_DIM_REDUCING_INLINE_U16_BUDGET: usize = 1280;

/// Number of per-launch base-pointer slots. Main-layer flat-path launches
/// use one slot per *backing* (not per class): up to 4 base read backings,
/// 4 base cache backings, 1-3 ext read backings, and 1 ext cache backing —
/// easily 10+ distinct Arcs per launch. 16 leaves comfortable headroom;
/// the 4-bit `ptr_idx` field in every u16 source encoding is sized to
/// match.
pub(crate) const GKR_DIM_REDUCING_BASE_SLOTS: usize = 16;

/// `(offset, count)` over the `inline_payload[GpuGKRSourceRecord]` array.
/// 4 B per range record.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct PayloadRange16 {
    pub(crate) offset: u16,
    pub(crate) count: u16,
}

/// One dim-reducing record (kernel-batch entry). 16 B with two PayloadRange16
/// slots, a u32 kind, and u16 batch-challenge metadata.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct GpuGKRDimensionReducingBatchRecordCompact {
    pub(crate) kind: u32,
    pub(crate) inputs: PayloadRange16,
    pub(crate) outputs: PayloadRange16,
    pub(crate) batch_challenge_offset: u16,
    pub(crate) batch_challenge_count: u16,
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

/// Compact replacement for `GpuGKRDimensionReducingRound0Batch<E>`.
/// ~3.7 KB by-value kernel-arg footprint.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingRound0BatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) _reserved1: u32,
    pub(crate) _reserved2: u32,
    pub(crate) eq_values: *const E,
    pub(crate) contributions: *mut E,
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_U16_BUDGET],
}

impl<E: Field> Default for GpuGKRDimensionReducingRound0BatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            _reserved1: 0,
            _reserved2: 0,
            eq_values: null(),
            contributions: null_mut(),
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_U16_BUDGET],
        }
    }
}

/// Compact replacement for `GpuGKRDimensionReducingRound{1,2,3}Batch<E>`.
/// Continuation rounds drop the `outputs` payload range (per-record reads
/// only) but otherwise share the round-0 layout. The kernel infers
/// `previous_layer_start` / `this_layer_start` / sizes from the per-launch
/// `step` plus the `bases` / `log2_stride` tables.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGKRDimensionReducingContinuationBatchCompact<E> {
    pub(crate) record_count: u32,
    pub(crate) _reserved0: u32,
    pub(crate) _reserved1: u32,
    pub(crate) _reserved2: u32,
    pub(crate) eq_values: *const E,
    pub(crate) contributions: *mut E,
    pub(crate) explicit_form: bool,
    pub(crate) _padding: [u8; 7],
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) records:
        [GpuGKRDimensionReducingBatchRecordCompact; GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
    pub(crate) inline_payload: [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_U16_BUDGET],
}

impl<E: Field> Default for GpuGKRDimensionReducingContinuationBatchCompact<E> {
    fn default() -> Self {
        Self {
            record_count: 0,
            _reserved0: 0,
            _reserved1: 0,
            _reserved2: 0,
            eq_values: null(),
            contributions: null_mut(),
            explicit_form: false,
            _padding: [0; 7],
            tables: GpuGKRDimensionReducingTables::default(),
            records: [GpuGKRDimensionReducingBatchRecordCompact::default();
                GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER],
            inline_payload: [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_INLINE_U16_BUDGET],
        }
    }
}

/// `(first_access, ptr_idx, poly_idx)` packed into a u16 source descriptor.
/// `first_access` is bit 15 (cheapest single-bit test on the GPU);
/// `ptr_idx` is bits 14..11 (4 bits, 16 slots); `poly_idx` is bits 10..0
/// (11 bits, up to 2048 polys per slot).
#[inline]
pub(crate) const fn pack_source_u16(first_access: bool, ptr_idx: u8, poly_idx: u16) -> u16 {
    let fa = if first_access { 1u16 << 15 } else { 0 };
    let p = ((ptr_idx as u16) & 0xF) << 11;
    let q = poly_idx & 0x07FF;
    fa | p | q
}

/// Cache half of a dual source record. Bit 15 is normally reserved and kept
/// clear; flat base virtual sources use it as a local discriminator because
/// their source half carries `first_access` plus a virtual source kind rather
/// than a real source pointer.
#[inline]
pub(crate) const fn pack_cache_u16(ptr_idx: u8, poly_idx: u16) -> u16 {
    let p = ((ptr_idx as u16) & 0xF) << 11;
    let q = poly_idx & 0x07FF;
    p | q
}
