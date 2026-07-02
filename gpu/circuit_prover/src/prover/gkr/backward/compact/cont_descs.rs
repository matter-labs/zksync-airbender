//! Compact descriptors for rounds 1, 2, and ≥ 3 (continuation).
//!
//! All three share a unified term table + per-tile metadata + a `fold_sources`
//! table. Their source arrays differ:
//!   - Round 1/2: split into `base_sources` (base-after-{one,two}) +
//!     `ext_sources` (continuing). Layer-uniform metadata
//!     (`base_layer_half_size`, `next_layer_size`, `base_quarter_size`)
//!     hoists out of every entry into descriptor-level u32s.
//!   - Continuation (rounds ≥ 3): one unified `sources` array of
//!     continuing-source u16s, plus per-slot `prev_per_poly_offset` /
//!     `cache_per_poly_offset` u32 tables.

use super::super::flat::{
    GpuFlatUnifiedTerm, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
    FLAT_CONT_MAX_SOURCES, FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS,
    FLAT_CONT_UNIFIED_MAX_TILES,
};
use super::super::kernels::{
    GpuGKRDimensionReducingTables, GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::kernel_limits::KERNEL_ARG_HARD_CEILING_BYTES;

// ---------------------------------------------------------------------------
// GpuFlatRound1UnifiedDesc
// ---------------------------------------------------------------------------

/// Compact mirror of `GpuFlatRound1UnifiedDesc`. Source pointer pairs collapse
/// to a single u16 each via `tables`; layer-uniform metadata (sizes) hoists
/// out of every per-source entry into descriptor-level `u32`s.
///
/// Must match CUDA `flat_round1_unified_desc_compact` in `backward/flat.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound1UnifiedDesc {
    pub(crate) tables: GpuGKRDimensionReducingTables,
    /// `base_poly_len / 2` — uniform across all base sources at this round.
    pub(crate) base_layer_half_size: u32,
    /// `fold_stride` for the ext-source pair lookup; matches the per-source
    /// `next_layer_size`.
    pub(crate) next_layer_size: u32,

    pub(crate) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(crate) num_ext_sources: u32,

    pub(crate) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound1UnifiedDesc {}
unsafe impl Sync for GpuFlatRound1UnifiedDesc {}

impl Default for GpuFlatRound1UnifiedDesc {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            terms: [GpuFlatUnifiedTerm::default(); FLAT_CONT_UNIFIED_MAX_TERMS],
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            tile_term_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            tile_fold_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound1UnifiedDesc>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound1UnifiedDesc exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// GpuFlatRound2UnifiedDesc
// ---------------------------------------------------------------------------

/// Compact mirror of `GpuFlatRound2UnifiedDesc`. Same shape as round 1 with
/// an extra `base_quarter_size` field for `base_after_two` semantics.
///
/// Must match CUDA `flat_round2_unified_desc_compact`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound2UnifiedDesc {
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) base_layer_half_size: u32,
    pub(crate) base_quarter_size: u32,
    pub(crate) next_layer_size: u32,

    pub(crate) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(crate) num_ext_sources: u32,

    pub(crate) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound2UnifiedDesc {}
unsafe impl Sync for GpuFlatRound2UnifiedDesc {}

impl Default for GpuFlatRound2UnifiedDesc {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            base_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            terms: [GpuFlatUnifiedTerm::default(); FLAT_CONT_UNIFIED_MAX_TERMS],
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            tile_term_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            tile_fold_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound2UnifiedDesc>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound2UnifiedDesc exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// GpuFlatContinuationUnifiedDesc
// ---------------------------------------------------------------------------

/// Compact mirror of `GpuFlatContinuationUnifiedDesc`. One unified source
/// array (mixes base- and ext-derived continuation sources — both end up
/// in per-poly folding caches by step ≥ 3). Each u16 carries
/// `(first_access, ptr_idx, poly_idx)`; the kernel resolves
/// `previous_layer_start` and `this_layer_cache_start` via `tables`.
///
/// `prev_per_poly_offset[ptr_idx]` and `cache_per_poly_offset[ptr_idx]`
/// give the element offsets within each per-poly slot of slot `ptr_idx`'s
/// consolidated folding backing where step S-1's data lives (prev) and
/// where step S writes (cache). The offset is uniform per slot but
/// **differs between slots** because base- and ext-derived caches have
/// different per-poly buffer sizes (`base_poly_size/2` vs. `poly_size`).
/// Both route into per-class consolidated Arcs, but the per-poly
/// arithmetic is independent for each.
///
/// The kernel resolves
/// `prev = (E*) tables.bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx]) + prev_per_poly_offset[ptr_idx]`
/// `cache = same + cache_per_poly_offset[ptr_idx]`.
///
/// Must match CUDA `flat_continuation_unified_desc_compact`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatContinuationUnifiedDesc {
    pub(crate) tables: GpuGKRDimensionReducingTables,

    /// Per-slot element offset of step S-1 data within each per-poly slot.
    pub(crate) prev_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
    /// Per-slot element offset of step S cache within each per-poly slot.
    pub(crate) cache_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],

    pub(crate) sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_SOURCES],
    pub(crate) num_sources: u32,

    pub(crate) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatContinuationUnifiedDesc {}
unsafe impl Sync for GpuFlatContinuationUnifiedDesc {}

impl Default for GpuFlatContinuationUnifiedDesc {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            prev_per_poly_offset: [0u32; GKR_DIM_REDUCING_BASE_SLOTS],
            cache_per_poly_offset: [0u32; GKR_DIM_REDUCING_BASE_SLOTS],
            sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_SOURCES],
            num_sources: 0,
            terms: [GpuFlatUnifiedTerm::default(); FLAT_CONT_UNIFIED_MAX_TERMS],
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            tile_term_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            tile_fold_offsets: [0u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatContinuationUnifiedDesc>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatContinuationUnifiedDesc exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// Device-pointer companions + term-tables bundle (Stage 3b)
// ---------------------------------------------------------------------------
//
// When a delegation's term/tile count overflows the inline __grid_constant__
// cap (keccak round-1 needs ~2500 terms), the three large arrays (`terms`,
// `tile_term_offsets`, `tile_fold_offsets`) move to device memory. Each
// inline desc gains a `_devptr` companion carrying only the remaining (small)
// fields — same field names/order so the templated CUDA helpers duck-type — and
// a `GpuFlatTermTables` bundle of the three device pointers is passed by value
// alongside. Fields removed vs. the inline structs: `terms`,
// `tile_term_offsets`, `tile_fold_offsets`. Everything else is identical.

/// Device pointers to the three large per-descriptor arrays that overflow the
/// inline cap on large delegations. Passed by value to the devptr-terms
/// kernels. Mirror of CUDA `flat_term_tables`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatTermTables {
    pub(crate) terms: *const GpuFlatUnifiedTerm,
    pub(crate) tile_term_offsets: *const u16,
    pub(crate) tile_fold_offsets: *const u16,
}

unsafe impl Send for GpuFlatTermTables {}
unsafe impl Sync for GpuFlatTermTables {}

impl Default for GpuFlatTermTables {
    fn default() -> Self {
        Self {
            terms: std::ptr::null(),
            tile_term_offsets: std::ptr::null(),
            tile_fold_offsets: std::ptr::null(),
        }
    }
}

/// Device-pointer companion of `GpuFlatRound1UnifiedDesc` (minus `terms`,
/// `tile_term_offsets`, `tile_fold_offsets`). Must match CUDA
/// `flat_round1_unified_desc_compact_devptr`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound1UnifiedDescDevptr {
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) base_layer_half_size: u32,
    pub(crate) next_layer_size: u32,

    pub(crate) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(crate) num_ext_sources: u32,

    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound1UnifiedDescDevptr {}
unsafe impl Sync for GpuFlatRound1UnifiedDescDevptr {}

impl Default for GpuFlatRound1UnifiedDescDevptr {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound1UnifiedDescDevptr>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound1UnifiedDescDevptr exceeds 32 KB inline ceiling",
    );
};

/// Device-pointer companion of `GpuFlatRound2UnifiedDesc`. Must match CUDA
/// `flat_round2_unified_desc_compact_devptr`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound2UnifiedDescDevptr {
    pub(crate) tables: GpuGKRDimensionReducingTables,
    pub(crate) base_layer_half_size: u32,
    pub(crate) base_quarter_size: u32,
    pub(crate) next_layer_size: u32,

    pub(crate) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(crate) num_ext_sources: u32,

    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound2UnifiedDescDevptr {}
unsafe impl Sync for GpuFlatRound2UnifiedDescDevptr {}

impl Default for GpuFlatRound2UnifiedDescDevptr {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            base_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound2UnifiedDescDevptr>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound2UnifiedDescDevptr exceeds 32 KB inline ceiling",
    );
};

/// Device-pointer companion of `GpuFlatContinuationUnifiedDesc`. Must match
/// CUDA `flat_continuation_unified_desc_compact_devptr`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatContinuationUnifiedDescDevptr {
    pub(crate) tables: GpuGKRDimensionReducingTables,

    pub(crate) prev_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
    pub(crate) cache_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],

    pub(crate) sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_SOURCES],
    pub(crate) num_sources: u32,

    pub(crate) num_terms: u32,
    pub(crate) num_constant_terms: u32,
    pub(crate) num_tiles: u32,
    pub(crate) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatContinuationUnifiedDescDevptr {}
unsafe impl Sync for GpuFlatContinuationUnifiedDescDevptr {}

impl Default for GpuFlatContinuationUnifiedDescDevptr {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            prev_per_poly_offset: [0u32; GKR_DIM_REDUCING_BASE_SLOTS],
            cache_per_poly_offset: [0u32; GKR_DIM_REDUCING_BASE_SLOTS],
            sources: [GpuGKRSourceRecord::default(); FLAT_CONT_MAX_SOURCES],
            num_sources: 0,
            num_terms: 0,
            num_constant_terms: 0,
            num_tiles: 0,
            fold_sources: [0u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatContinuationUnifiedDescDevptr>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatContinuationUnifiedDescDevptr exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// Host-side term/tile tables (Stage 3b device-terms path)
// ---------------------------------------------------------------------------

/// The three large per-descriptor arrays (`terms`, `tile_term_offsets`,
/// `tile_fold_offsets`) as host Vecs sized to their actual counts. Produced by
/// the desc builders when the count would overflow the inline `__grid_constant__`
/// cap; H2D-uploaded into device buffers and consumed via `GpuFlatTermTables`
/// pointers by the `_devptr_terms_` kernels. Bit-identical contents to the
/// inline arrays — only the storage location differs.
#[derive(Clone)]
pub(crate) struct FlatTermTablesHost {
    pub(crate) terms: Vec<GpuFlatUnifiedTerm>,
    pub(crate) tile_term_offsets: Vec<u16>,
    pub(crate) tile_fold_offsets: Vec<u16>,
}

impl GpuFlatRound1UnifiedDesc {
    /// Copy the small (non-term/tile) fields into the device-pointer companion.
    /// The `terms`/`tile_*` arrays are omitted — they live in device memory.
    pub(crate) fn to_devptr(&self) -> GpuFlatRound1UnifiedDescDevptr {
        GpuFlatRound1UnifiedDescDevptr {
            tables: self.tables,
            base_layer_half_size: self.base_layer_half_size,
            next_layer_size: self.next_layer_size,
            base_sources: self.base_sources,
            num_base_sources: self.num_base_sources,
            ext_sources: self.ext_sources,
            num_ext_sources: self.num_ext_sources,
            num_terms: self.num_terms,
            num_constant_terms: self.num_constant_terms,
            num_tiles: self.num_tiles,
            fold_sources: self.fold_sources,
        }
    }
}

impl GpuFlatRound2UnifiedDesc {
    pub(crate) fn to_devptr(&self) -> GpuFlatRound2UnifiedDescDevptr {
        GpuFlatRound2UnifiedDescDevptr {
            tables: self.tables,
            base_layer_half_size: self.base_layer_half_size,
            base_quarter_size: self.base_quarter_size,
            next_layer_size: self.next_layer_size,
            base_sources: self.base_sources,
            num_base_sources: self.num_base_sources,
            ext_sources: self.ext_sources,
            num_ext_sources: self.num_ext_sources,
            num_terms: self.num_terms,
            num_constant_terms: self.num_constant_terms,
            num_tiles: self.num_tiles,
            fold_sources: self.fold_sources,
        }
    }
}

impl GpuFlatContinuationUnifiedDesc {
    pub(crate) fn to_devptr(&self) -> GpuFlatContinuationUnifiedDescDevptr {
        GpuFlatContinuationUnifiedDescDevptr {
            tables: self.tables,
            prev_per_poly_offset: self.prev_per_poly_offset,
            cache_per_poly_offset: self.cache_per_poly_offset,
            sources: self.sources,
            num_sources: self.num_sources,
            num_terms: self.num_terms,
            num_constant_terms: self.num_constant_terms,
            num_tiles: self.num_tiles,
            fold_sources: self.fold_sources,
        }
    }
}
