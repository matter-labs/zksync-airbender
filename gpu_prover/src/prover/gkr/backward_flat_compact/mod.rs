//! Compact descriptors for the GKR backward main-layer flat path.
//!
//! Each per-launch source pointer collapses to a `u16` packed
//! `(virtual?/slot, poly_idx)` reference, with a small per-launch `tables`
//! block (`bases[8]` / `log2_stride[16]`) that the kernel uses to resolve
//! the byte address. Term tables (`c0_bf`, `c0_ext`, `c1_*`, `c1_linear`,
//! etc.) use u16 source indices.
//!
//! Round 0's source u16 has no folding cache, so bit 15 doubles as
//! `is_virtual`.

// rustc's dead-code analysis under --lib --tests under-reports usage through
// some of the generic impl chains in `backward.rs` (e.g. `prepare_layer_from_blueprints`
// on `GpuGKRDimensionReducingBackwardState`). Parity tests exercise every
// public function in this module under `--release`. Suppress the false
// positives at module scope.
#![allow(dead_code)]

mod round12_descs;

pub(super) use round12_descs::{
    build_flat_round1_unified_desc_compact, build_flat_round2_unified_desc_compact,
};

use super::backward_flat::{
    CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair, GpuFlatUnifiedTerm, FLAT_CONT_MAX_BASE_SOURCES,
    FLAT_CONT_MAX_EXT_SOURCES, FLAT_CONT_MAX_SOURCES, FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES,
    FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES, FLAT_ROUND0_MAX_C0_BF,
    FLAT_ROUND0_MAX_C0_EXT, FLAT_ROUND0_MAX_C1_BF_BF, FLAT_ROUND0_MAX_C1_BF_E4,
    FLAT_ROUND0_MAX_C1_E4_E4, FLAT_ROUND0_MAX_C1_LINEAR, FLAT_ROUND0_MAX_SOURCES,
};
use super::backward_kernels::{
    gkr_dim_reducing_launch_config, pack_cache_u16, pack_source_u16, GpuGKRDimensionReducingTables,
    GpuGKRSourceRecord, GKR_BACKWARD_MAX_TRACE_LEN_LOG2, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::GpuGKRStorage;
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use era_cudart::cuda_kernel_declaration;
use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::cudaGetSymbolAddress;
use field::Field;
use std::ffi::c_void;
use std::ptr::null_mut;
use std::sync::OnceLock;

/// Hard ceiling: kernel arguments must fit in `cudaLaunchKernelExC`'s 32 KB
/// inline parameter area. Any descriptor whose size exceeds this fails the
/// build (see compile-time assertions below).
pub(super) const KERNEL_ARG_HARD_CEILING_BYTES: usize = 32 * 1024;

/// Soft target: keep descriptors under 16 KB for headroom against future
/// table growth without re-bumping back into H2D territory.
pub(super) const KERNEL_ARG_SOFT_TARGET_BYTES: usize = 16 * 1024;
/// Main-layer next-layer state stores `(folding_steps - 1)` per-round
/// challenges plus 2 transcript-squeezed values: `[folding_challenges,
/// last_r, next_batching]`.
pub(super) const MAX_MAIN_LAYER_CLAIM_POINT_LEN: usize = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;

// ---------------------------------------------------------------------------
// u16 source encoding (round 0)
// ---------------------------------------------------------------------------
//
// Layout of each `u16` in `GpuFlatRound0StaticDescCompact::sources[]`:
//
//   bit 15      : is_virtual (1 = virtual base-field source, 0 = real consolidated poly)
//   bits 14..11 : ptr_idx into `tables.bases` / `tables.log2_stride` (real path, 4 bits / 16 slots)
//   bits 10..0  : poly_idx within the chosen slot (real path, 11 bits / max 2048) OR
//                 low 3 bits = `gkr_base_source_kind` for the virtual path
//                 (high bits zero by construction)
//
// Decoder (CUDA, mirrors `flat_load_bf_value` semantics):
//
//   u16 packed = desc.sources[idx];
//   if (packed & 0x8000) {
//     auto kind = static_cast<gkr_base_source_kind>(packed & 0x7);
//     return gkr_virtual_base_value(kind, gid);
//   }
//   auto slot     = (packed >> 11) & 0xF;
//   auto poly_idx = packed & 0x07FF;
//   auto* base_T  = reinterpret_cast<const T*>(tables.bases[slot]);
//   return load(base_T + (poly_idx << tables.log2_stride[slot]), gid);

const FLAT_SOURCE_VIRTUAL_FLAG: u16 = 0x8000;
// 4-bit ptr_idx (16 slots) shifted by 11; 11-bit poly_idx (max 2048).
const FLAT_SOURCE_PTR_IDX_SHIFT: u32 = 11;
const FLAT_SOURCE_PTR_IDX_MASK: u16 = 0xF;
const FLAT_SOURCE_POLY_IDX_MASK: u16 = 0x07FF;
const FLAT_SOURCE_VIRTUAL_KIND_MASK: u16 = 0x7;

/// Pack a real consolidated-poly source reference. `slot` indexes
/// `tables.bases`/`tables.log2_stride`; `poly_idx` is the per-class poly
/// index within that backing.
#[inline]
pub(super) fn pack_flat_round0_source_real(slot: u8, poly_idx: u16) -> u16 {
    debug_assert!(
        (slot as usize) < GKR_DIM_REDUCING_BASE_SLOTS,
        "flat round0 slot {slot} >= GKR_DIM_REDUCING_BASE_SLOTS={GKR_DIM_REDUCING_BASE_SLOTS}",
    );
    debug_assert!(
        poly_idx <= FLAT_SOURCE_POLY_IDX_MASK,
        "flat round0 poly_idx {poly_idx} exceeds 11-bit budget {FLAT_SOURCE_POLY_IDX_MASK}",
    );
    ((slot as u16) << FLAT_SOURCE_PTR_IDX_SHIFT) | (poly_idx & FLAT_SOURCE_POLY_IDX_MASK)
}

/// Pack a virtual base-field source (range-check, inits/teardowns). `kind`
/// must be one of the `gkr_base_source_kind` discriminants in
/// [0, 7] (low 3 bits).
#[inline]
pub(super) fn pack_flat_round0_source_virtual(kind: u8) -> u16 {
    debug_assert!(
        (kind as u16) <= FLAT_SOURCE_VIRTUAL_KIND_MASK,
        "flat round0 virtual kind {kind} exceeds 3-bit budget",
    );
    FLAT_SOURCE_VIRTUAL_FLAG | (kind as u16 & FLAT_SOURCE_VIRTUAL_KIND_MASK)
}

/// Decoded view of a packed flat round-0 source. Used by tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum UnpackedFlatRound0Source {
    Real { slot: u8, poly_idx: u16 },
    Virtual { kind: u8 },
}

#[inline]
pub(super) fn unpack_flat_round0_source(packed: u16) -> UnpackedFlatRound0Source {
    if (packed & FLAT_SOURCE_VIRTUAL_FLAG) != 0 {
        UnpackedFlatRound0Source::Virtual {
            kind: (packed & FLAT_SOURCE_VIRTUAL_KIND_MASK) as u8,
        }
    } else {
        UnpackedFlatRound0Source::Real {
            slot: ((packed >> FLAT_SOURCE_PTR_IDX_SHIFT) & FLAT_SOURCE_PTR_IDX_MASK) as u8,
            poly_idx: packed & FLAT_SOURCE_POLY_IDX_MASK,
        }
    }
}

// ---------------------------------------------------------------------------
// GpuFlatRound0StaticDescCompact
// ---------------------------------------------------------------------------

/// Compact flat round-0 static descriptor. Source pointers are u16 packed
/// references; term tables stay as in the verbose descriptor. Passed by
/// value as `__grid_constant__`.
///
/// Must match CUDA `flat_round0_static_desc_compact` in `flat_backward.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound0StaticDescCompact {
    pub(super) tables: GpuGKRDimensionReducingTables,

    pub(super) sources: [GpuGKRSourceRecord; FLAT_ROUND0_MAX_SOURCES],
    pub(super) num_sources: u32,

    pub(super) c0_bf: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_BF],
    pub(super) num_c0_bf: u32,
    pub(super) c0_ext: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_EXT],
    pub(super) num_c0_ext: u32,

    pub(super) c1_bf_bf: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_BF],
    pub(super) num_c1_bf_bf: u32,
    pub(super) c1_e4_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_E4_E4],
    pub(super) num_c1_e4_e4: u32,
    pub(super) c1_bf_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_E4],
    pub(super) num_c1_bf_e4: u32,

    pub(super) c1_linear: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C1_LINEAR],
    pub(super) num_c1_linear: u32,
}

unsafe impl Send for GpuFlatRound0StaticDescCompact {}
unsafe impl Sync for GpuFlatRound0StaticDescCompact {}

impl Default for GpuFlatRound0StaticDescCompact {
    fn default() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            sources: [GpuGKRSourceRecord::default(); FLAT_ROUND0_MAX_SOURCES],
            num_sources: 0,
            c0_bf: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C0_BF],
            num_c0_bf: 0,
            c0_ext: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C0_EXT],
            num_c0_ext: 0,
            c1_bf_bf: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_BF_BF],
            num_c1_bf_bf: 0,
            c1_e4_e4: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_E4_E4],
            num_c1_e4_e4: 0,
            c1_bf_e4: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_BF_E4],
            num_c1_bf_e4: 0,
            c1_linear: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C1_LINEAR],
            num_c1_linear: 0,
        }
    }
}

// Compile-time size invariant: must fit in cudaLaunchKernelExC's 32 KB inline
// parameter area.
const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound0StaticDescCompact>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound0StaticDescCompact exceeds the 32 KB cudaLaunchKernelExC inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// Build plan: compact static desc + recipes (mirror of FlatRound0BuildPlan)
// ---------------------------------------------------------------------------

/// Compact mirror of `FlatRound0BuildPlan` with the compact static descriptor.
pub(super) struct FlatRound0BuildPlanCompact<E> {
    pub(super) static_desc: Box<GpuFlatRound0StaticDescCompact>,
    pub(super) recipes: Vec<CoefficientRecipe<E>>,
}

// ---------------------------------------------------------------------------
// Reverse map: raw poly start pointer -> (backing base, log2_stride, poly_idx)
// ---------------------------------------------------------------------------
//
// Round-0 sources can reference polys at multiple storage layers (e.g. layer-0
// trace/witness/setup polys plus layer-N gate-output polys). We flatten the
// storage's per-layer `{base,ext}_class_backings` Arcs into a sortable list of
// byte ranges, then range-map each `*const u8` pointer to the backing it
// falls in. Slot indices are assigned in first-appearance order across the
// build walk, dedup keyed on the raw pointer — matching the behavior of
// `FlatDescriptionBuilder::source_map`.

#[derive(Clone, Copy)]
pub(super) struct BackingRange {
    /// Backing base (cast to `*const u8` for ABI uniformity with `tables.bases`).
    pub(super) base: *const u8,
    /// `start_byte..end_byte` half-open range of valid pointer addresses
    /// inside this backing.
    pub(super) start_byte: usize,
    pub(super) end_byte: usize,
    /// Element size of the backing (4 for base-field, 16 for ext-field on E4).
    pub(super) elem_bytes: usize,
    /// Per-poly stride in elements (= layer's `log2_stride`).
    pub(super) log2_stride: u32,
}

pub(super) fn build_backing_ranges<E: Field>(storage: &GpuGKRStorage<BF, E>) -> Vec<BackingRange> {
    let mut ranges = Vec::with_capacity(64);
    let layout = storage
        .layout
        .as_ref()
        .expect("compact flat encoder requires storage layout");
    for (layer_idx, layer) in storage.layers.iter().enumerate() {
        if layer_idx >= layout.layers.len() {
            // Round 0 reads only artifact and base-layer polys, so any pointer
            // referencing a tower layer past the artifact range should be
            // unreachable here. Skip safely.
            continue;
        }
        let layer_layout = &layout.layers[layer_idx];
        let log2_stride = layer_layout.log2_stride;
        for backing in layer.base_class_backings.values() {
            let len_bytes = backing.len() * std::mem::size_of::<BF>();
            let base = backing.as_ptr() as *const u8;
            let start = base as usize;
            ranges.push(BackingRange {
                base,
                start_byte: start,
                end_byte: start + len_bytes,
                elem_bytes: std::mem::size_of::<BF>(),
                log2_stride,
            });
        }
        for backing in layer.ext_class_backings.values() {
            let len_bytes = backing.len() * std::mem::size_of::<E>();
            let base = backing.as_ptr() as *const u8;
            let start = base as usize;
            ranges.push(BackingRange {
                base,
                start_byte: start,
                end_byte: start + len_bytes,
                elem_bytes: std::mem::size_of::<E>(),
                log2_stride,
            });
        }
    }
    ranges
}

/// Resolve a `*const u8` source pointer into the backing it falls in.
/// Returns `(backing_base, log2_stride, poly_idx)`.
pub(super) fn resolve_backing_for_pointer(
    ranges: &[BackingRange],
    ptr: *const u8,
) -> Option<(*const u8, u32, u16)> {
    let p = ptr as usize;
    for r in ranges {
        if p >= r.start_byte && p < r.end_byte {
            let byte_offset = p - r.start_byte;
            debug_assert_eq!(
                byte_offset % r.elem_bytes,
                0,
                "pointer {p:#x} not aligned to {elem}-byte element boundary in backing [{s:#x}..{e:#x})",
                elem = r.elem_bytes,
                s = r.start_byte,
                e = r.end_byte,
            );
            let element_offset = byte_offset / r.elem_bytes;
            let stride = 1usize << r.log2_stride;
            debug_assert_eq!(
                element_offset % stride,
                0,
                "pointer {p:#x} element_offset {element_offset} not a multiple of stride {stride}",
            );
            let poly_idx_usize = element_offset >> r.log2_stride;
            assert!(
                poly_idx_usize <= FLAT_SOURCE_POLY_IDX_MASK as usize,
                "compact flat: poly_idx {poly_idx_usize} exceeds 11-bit budget",
            );
            return Some((r.base, r.log2_stride, poly_idx_usize as u16));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Round 1 / Round 2 / Continuation compact descriptors
// ---------------------------------------------------------------------------
//
// These three descriptors all share:
//   - a unified term table (`GpuFlatUnifiedTerm`, already u16-indexed)
//   - per-tile metadata (`tile_term_offsets`, `tile_fold_offsets`)
//   - a `fold_sources: [u16; ...]` table
//
// Their source arrays differ:
//   - Continuation (rounds ≥ 3): one `sources` array of continuing-source u16s.
//   - Round 1: split into `base_sources` (base-after-one) + `ext_sources`
//     (continuing). Layer-uniform metadata (`base_layer_half_size`,
//     `next_layer_size`) hoists out of every entry into descriptor-level u32s.
//   - Round 2: same shape as round 1, with `base_after_two` semantics. Adds
//     `base_quarter_size` to the layer-uniform metadata.
//
// Source u16 encoding (rounds 1+):
//
// ext_sources (no virtual variant):
//   bit 15      : `first_access` — 1 ⇒ read from previous_layer slot,
//                 fold into cache. 0 ⇒ read from cache (and overwrite).
//   bits 14..11 : `ptr_idx` (4 bits / 16 slots) into `tables.bases`
//                 holding the previous-layer backing.
//   bits 10..0  : `poly_idx` (11 bits / max 2048) within that backing.
//
// base_sources (round 1/2 only — continuation has no base sources):
//   bit 15      : `first_access` (same semantics as ext).
//   bit 14      : `is_virtual` — 1 ⇒ low 3 bits encode `gkr_base_source_kind`.
//   bits 13..10 : `ptr_idx` (4 bits / 16 slots) — real path slot index, or
//                 virtual_cache_slot for the virtual path.
//   bits 9..0   : `poly_idx` (10 bits / max 1024) — real path. For the virtual
//                 path the low 3 bits are `gkr_base_source_kind`.
//
// The matching cache slot is carried by the record's cache half, so source
// and cache poly indices can differ for copy aliases.
//
// Per-launch metadata cost: 128 B for `tables`. Each source descriptor is
// 2 B.

// ---------------------------------------------------------------------------
// Bit-mask constants for rounds 1+ source encoding
// ---------------------------------------------------------------------------

/// Round 1+ ext_source u16 layout (no base/virtual distinction):
///   bit 15      : first_access
///   bits 14..11 : ptr_idx (4 bits, 16 slots)
///   bits 10..0  : poly_idx (11 bits, max 2048)
const CONT_EXT_FIRST_ACCESS_FLAG: u16 = 0x8000;
const CONT_EXT_PTR_IDX_SHIFT: u32 = 11;
const CONT_EXT_PTR_IDX_MASK: u16 = 0xF;
const CONT_EXT_POLY_IDX_MASK: u16 = 0x07FF;

/// Round 1/2 base_source u16 layout:
///   bit 15      : first_access
///   bit 14      : is_virtual
///   bits 13..10 : ptr_idx (4 bits, 16 slots) — real path OR virtual_cache_slot (virtual)
///   bits 9..0   : poly_idx (10 bits, max 1024) — real path OR low 3 bits = source_kind (virtual)
pub(super) const CONT_BASE_FIRST_ACCESS_FLAG: u16 = 0x8000;
const CONT_BASE_VIRTUAL_FLAG: u16 = 0x4000;
pub(super) const CONT_BASE_CACHE_VIRTUAL_FLAG: u16 = 0x8000;
const CONT_BASE_PTR_IDX_SHIFT: u32 = 10;
const CONT_BASE_PTR_IDX_MASK: u16 = 0xF;
const CONT_BASE_POLY_IDX_MASK: u16 = 0x03FF;
pub(super) const CONT_BASE_VIRTUAL_KIND_MASK: u16 = 0x7;

#[inline]
pub(super) fn pack_cont_ext_source(first_access: bool, slot: u8, poly_idx: u16) -> u16 {
    debug_assert!((slot as u16) <= CONT_EXT_PTR_IDX_MASK);
    debug_assert!(poly_idx <= CONT_EXT_POLY_IDX_MASK);
    let first_bit = if first_access {
        CONT_EXT_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit | ((slot as u16) << CONT_EXT_PTR_IDX_SHIFT) | (poly_idx & CONT_EXT_POLY_IDX_MASK)
}

#[inline]
pub(super) fn pack_cont_base_source_real(first_access: bool, slot: u8, poly_idx: u16) -> u16 {
    debug_assert!((slot as u16) <= CONT_BASE_PTR_IDX_MASK);
    debug_assert!(poly_idx <= CONT_BASE_POLY_IDX_MASK);
    let first_bit = if first_access {
        CONT_BASE_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit | ((slot as u16) << CONT_BASE_PTR_IDX_SHIFT) | (poly_idx & CONT_BASE_POLY_IDX_MASK)
}

/// Pack a virtual base source. `cache_slot` is the index in
/// `tables.bases` holding the virtual cache backing
/// (`intermediate_base_folding_consolidated.virtual_per_class[class]`).
/// `kind` is the `GpuBaseFieldSourceKind` discriminant (2..=5 for the four
/// virtual variants); the kernel synthesizes the value by calling
/// `gkr_virtual_base_value(kind, gid)`.
///
/// poly_idx within the virtual cache backing comes from
/// `virtual_index[poly]` and is encoded into the descriptor's
/// `virtual_cache_poly_idx` table (per-source array), so the source u16
/// itself doesn't need to carry it for the virtual path.
#[inline]
pub(super) fn pack_cont_base_source_virtual(first_access: bool, cache_slot: u8, kind: u8) -> u16 {
    debug_assert!((cache_slot as u16) <= CONT_BASE_PTR_IDX_MASK);
    debug_assert!((kind as u16) <= CONT_BASE_VIRTUAL_KIND_MASK);
    let first_bit = if first_access {
        CONT_BASE_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit
        | CONT_BASE_VIRTUAL_FLAG
        | ((cache_slot as u16) << CONT_BASE_PTR_IDX_SHIFT)
        | ((kind as u16) & CONT_BASE_VIRTUAL_KIND_MASK)
}

/// Decoded view of a packed continuation ext-source u16.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct UnpackedContExtSource {
    pub(super) first_access: bool,
    pub(super) slot: u8,
    pub(super) poly_idx: u16,
}

#[inline]
pub(super) fn unpack_cont_ext_source(packed: u16) -> UnpackedContExtSource {
    UnpackedContExtSource {
        first_access: (packed & CONT_EXT_FIRST_ACCESS_FLAG) != 0,
        slot: ((packed >> CONT_EXT_PTR_IDX_SHIFT) & CONT_EXT_PTR_IDX_MASK) as u8,
        poly_idx: packed & CONT_EXT_POLY_IDX_MASK,
    }
}

/// Decoded view of a packed continuation base-source u16.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum UnpackedContBaseSource {
    Real {
        first_access: bool,
        slot: u8,
        poly_idx: u16,
    },
    Virtual {
        first_access: bool,
        cache_slot: u8,
        kind: u8,
    },
}

#[inline]
pub(super) fn unpack_cont_base_source(packed: u16) -> UnpackedContBaseSource {
    let first_access = (packed & CONT_BASE_FIRST_ACCESS_FLAG) != 0;
    if (packed & CONT_BASE_VIRTUAL_FLAG) != 0 {
        UnpackedContBaseSource::Virtual {
            first_access,
            cache_slot: ((packed >> CONT_BASE_PTR_IDX_SHIFT) & CONT_BASE_PTR_IDX_MASK) as u8,
            kind: (packed & CONT_BASE_VIRTUAL_KIND_MASK) as u8,
        }
    } else {
        UnpackedContBaseSource::Real {
            first_access,
            slot: ((packed >> CONT_BASE_PTR_IDX_SHIFT) & CONT_BASE_PTR_IDX_MASK) as u8,
            poly_idx: packed & CONT_BASE_POLY_IDX_MASK,
        }
    }
}

// ---------------------------------------------------------------------------
// GpuFlatRound1UnifiedDescCompact
// ---------------------------------------------------------------------------

/// Compact mirror of `GpuFlatRound1UnifiedDesc`. Source pointer pairs collapse
/// to a single u16 each via `tables`; layer-uniform metadata (sizes) hoists
/// out of every per-source entry into descriptor-level `u32`s.
///
/// Must match CUDA `flat_round1_unified_desc_compact` in `flat_backward.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound1UnifiedDescCompact {
    pub(super) tables: GpuGKRDimensionReducingTables,
    /// `base_poly_len / 2` — uniform across all base sources at this round.
    pub(super) base_layer_half_size: u32,
    /// `fold_stride` for the ext-source pair lookup; matches the per-source
    /// `next_layer_size`.
    pub(super) next_layer_size: u32,

    pub(super) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(super) num_ext_sources: u32,

    pub(super) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(super) num_terms: u32,
    pub(super) num_constant_terms: u32,
    pub(super) num_tiles: u32,
    pub(super) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound1UnifiedDescCompact {}
unsafe impl Sync for GpuFlatRound1UnifiedDescCompact {}

impl Default for GpuFlatRound1UnifiedDescCompact {
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
        std::mem::size_of::<GpuFlatRound1UnifiedDescCompact>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound1UnifiedDescCompact exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// GpuFlatRound2UnifiedDescCompact
// ---------------------------------------------------------------------------

/// Compact mirror of `GpuFlatRound2UnifiedDesc`. Same shape as round 1 with
/// an extra `base_quarter_size` field for `base_after_two` semantics.
///
/// Must match CUDA `flat_round2_unified_desc_compact`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound2UnifiedDescCompact {
    pub(super) tables: GpuGKRDimensionReducingTables,
    pub(super) base_layer_half_size: u32,
    pub(super) base_quarter_size: u32,
    pub(super) next_layer_size: u32,

    pub(super) base_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_BASE_SOURCES],
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_EXT_SOURCES],
    pub(super) num_ext_sources: u32,

    pub(super) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(super) num_terms: u32,
    pub(super) num_constant_terms: u32,
    pub(super) num_tiles: u32,
    pub(super) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatRound2UnifiedDescCompact {}
unsafe impl Sync for GpuFlatRound2UnifiedDescCompact {}

impl Default for GpuFlatRound2UnifiedDescCompact {
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
        std::mem::size_of::<GpuFlatRound2UnifiedDescCompact>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound2UnifiedDescCompact exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// GpuFlatContinuationUnifiedDescCompact
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
pub(crate) struct GpuFlatContinuationUnifiedDescCompact {
    pub(super) tables: GpuGKRDimensionReducingTables,

    /// Per-slot element offset of step S-1 data within each per-poly slot.
    pub(super) prev_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
    /// Per-slot element offset of step S cache within each per-poly slot.
    pub(super) cache_per_poly_offset: [u32; GKR_DIM_REDUCING_BASE_SLOTS],

    pub(super) sources: [GpuGKRSourceRecord; FLAT_CONT_MAX_SOURCES],
    pub(super) num_sources: u32,

    pub(super) terms: [GpuFlatUnifiedTerm; FLAT_CONT_UNIFIED_MAX_TERMS],
    pub(super) num_terms: u32,
    pub(super) num_constant_terms: u32,
    pub(super) num_tiles: u32,
    pub(super) tile_term_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) tile_fold_offsets: [u16; FLAT_CONT_UNIFIED_MAX_TILES + 1],
    pub(super) fold_sources: [u16; FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES],
}

unsafe impl Send for GpuFlatContinuationUnifiedDescCompact {}
unsafe impl Sync for GpuFlatContinuationUnifiedDescCompact {}

impl Default for GpuFlatContinuationUnifiedDescCompact {
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
        std::mem::size_of::<GpuFlatContinuationUnifiedDescCompact>()
            <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatContinuationUnifiedDescCompact exceeds 32 KB inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// CUDA kernel declarations + launchers (compact path)
// ---------------------------------------------------------------------------
//
// Mirror `launch_main_round0_flat` / `launch_main_round0_flat_constant` in
// `backward_flat.rs` but bind to the compact descriptor. Same launch config —
// the CUDA kernel's grid/block math depends on `acc_size` only.

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound0FlatCompact<T>,
    static_desc: GpuFlatRound0StaticDescCompact,
    coefficients: *const T,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round0_flat_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDescCompact,
        coefficients: *const E4,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) trait GpuFlatRound0CompactKernelSet: Field {
    const MAIN_ROUND0_FLAT_COMPACT: GpuGKRMainRound0FlatCompactSignature<Self>;
}

impl GpuFlatRound0CompactKernelSet for E4 {
    const MAIN_ROUND0_FLAT_COMPACT: GpuGKRMainRound0FlatCompactSignature<Self> =
        ab_gkr_main_round0_flat_compact_e4_kernel;
}

pub(super) fn launch_main_round0_flat_compact<E: GpuFlatRound0CompactKernelSet>(
    static_desc: &GpuFlatRound0StaticDescCompact,
    coefficients: *const E,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatCompactArguments::new(
        *static_desc,
        coefficients,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatCompactFunction(E::MAIN_ROUND0_FLAT_COMPACT).launch(&config, &args)
}

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound0FlatConstantCompact<T>,
    static_desc: GpuFlatRound0StaticDescCompact,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round0_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDescCompact,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) trait GpuFlatRound0ConstantCompactKernelSet: Field {
    const MAIN_ROUND0_FLAT_CONSTANT_COMPACT: GpuGKRMainRound0FlatConstantCompactSignature<Self>;
}

impl GpuFlatRound0ConstantCompactKernelSet for E4 {
    const MAIN_ROUND0_FLAT_CONSTANT_COMPACT: GpuGKRMainRound0FlatConstantCompactSignature<Self> =
        ab_gkr_main_round0_flat_constant_compact_e4_kernel;
}

pub(super) fn launch_main_round0_flat_constant_compact<E: GpuFlatRound0ConstantCompactKernelSet>(
    static_desc: &GpuFlatRound0StaticDescCompact,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatConstantCompactArguments::new(
        *static_desc,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatConstantCompactFunction(E::MAIN_ROUND0_FLAT_CONSTANT_COMPACT)
        .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Continuation reverse-map (rounds ≥ 3): consolidated folding backings
// ---------------------------------------------------------------------------
//
// `previous_layer_start` and `this_layer_cache_start` for round 1+ ext
// sources both point into `GpuGKRLayerSource::intermediate_folding_consolidated`,
// at sub-offsets within each per-poly slot. The reverse-map below indexes
// every consolidated folding backing across all layers and resolves a raw
// `*const u8` to `(base, per_poly_log2_stride, poly_idx, sub_offset_in_elements)`.

#[derive(Clone, Copy)]
struct ContinuationBackingRange {
    base: *const u8,
    start_byte: usize,
    end_byte: usize,
    elem_bytes: usize,
    /// `log2(per_poly_size_in_elements)`. The consolidated folding backing's
    /// per-poly stride matches the layer layout's `log2_stride`.
    log2_stride: u32,
}

fn build_continuation_backing_ranges<E: Field>(
    storage: &GpuGKRStorage<BF, E>,
) -> Vec<ContinuationBackingRange> {
    let mut ranges = Vec::with_capacity(64);
    let layout = storage
        .layout
        .as_ref()
        .expect("compact continuation encoder requires storage layout");
    for (layer_idx, layer) in storage.layers.iter().enumerate() {
        let layer_layout = match layout.layers.get(layer_idx) {
            Some(l) => l,
            None => continue,
        };
        let log2_stride = layer_layout.log2_stride;
        if let Some(consolidated) = layer.intermediate_folding_consolidated.as_ref() {
            debug_assert_eq!(
                consolidated.per_poly_size,
                1usize << log2_stride,
                "consolidated ext-folding per_poly_size {} mismatches layout 1<<{} at layer {layer_idx}",
                consolidated.per_poly_size,
                log2_stride,
            );
            for backing in consolidated.per_class.values() {
                let len_bytes = backing.len() * std::mem::size_of::<E>();
                let base = backing.as_ptr() as *const u8;
                let start = base as usize;
                ranges.push(ContinuationBackingRange {
                    base,
                    start_byte: start,
                    end_byte: start + len_bytes,
                    elem_bytes: std::mem::size_of::<E>(),
                    log2_stride,
                });
            }
        }
        // Continuation reads also pull from per-poly base-field folding
        // caches. Those Arcs land here too — same E element type, but the
        // per-poly buffer is half the layout stride (`base_poly_size / 2`).
        // The encoder's stride is the per-poly offset within the
        // consolidated Arc; the layout's `log2_stride` is the natural log2
        // of that per-poly buffer for this layer.
        if let Some(consolidated) = layer.intermediate_base_folding_consolidated.as_ref() {
            let base_log2 = consolidated.per_poly_size.trailing_zeros();
            debug_assert!(
                consolidated.per_poly_size.is_power_of_two() && consolidated.per_poly_size > 0,
                "consolidated base-folding per_poly_size {} must be a positive power of two at layer {layer_idx}",
                consolidated.per_poly_size,
            );
            for backing in consolidated
                .per_class
                .values()
                .chain(consolidated.virtual_per_class.values())
            {
                let len_bytes = backing.len() * std::mem::size_of::<E>();
                let base = backing.as_ptr() as *const u8;
                let start = base as usize;
                ranges.push(ContinuationBackingRange {
                    base,
                    start_byte: start,
                    end_byte: start + len_bytes,
                    elem_bytes: std::mem::size_of::<E>(),
                    log2_stride: base_log2,
                });
            }
        }
    }
    ranges
}

/// Resolve a raw `*const u8` pointer into a continuation consolidated
/// backing. Returns `(base, log2_stride, poly_idx, sub_offset_in_elements)`
/// — the sub-offset is the per-poly element offset for the prev/cache
/// pointer (per-step uniform).
fn resolve_continuation_backing_for_pointer(
    ranges: &[ContinuationBackingRange],
    ptr: *const u8,
) -> Option<(*const u8, u32, u16, u32)> {
    let p = ptr as usize;
    for r in ranges {
        if p >= r.start_byte && p < r.end_byte {
            let byte_offset = p - r.start_byte;
            assert_eq!(
                byte_offset % r.elem_bytes,
                0,
                "compact continuation: pointer {p:#x} not aligned to {}-byte element boundary",
                r.elem_bytes,
            );
            let element_offset = byte_offset / r.elem_bytes;
            let stride = 1usize << r.log2_stride;
            let poly_idx_usize = element_offset >> r.log2_stride;
            let sub_offset = element_offset & (stride - 1);
            assert!(
                poly_idx_usize <= FLAT_SOURCE_POLY_IDX_MASK as usize,
                "compact continuation: poly_idx {poly_idx_usize} exceeds 11-bit budget",
            );
            return Some((
                r.base,
                r.log2_stride,
                poly_idx_usize as u16,
                sub_offset as u32,
            ));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Builder: per-step source array + plan term_desc → compact unified desc
// ---------------------------------------------------------------------------
//
// Resolves each `(prev, cache)` pointer pair against the consolidated folding
// backings, populates compact `tables` + `sources[]` + per-poly offsets,
// and builds the term / tile / fold metadata from `plan.term_desc` in one
// pass. Each sumcheck step gets its own `sources` array (different cache
// pointers per step), and the term arrays in `plan.term_desc` are shared.
pub(super) fn build_flat_continuation_unified_desc_compact<E: Field>(
    sources: &[super::backward_flat::GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES],
    plan: &super::backward_flat::FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Box<GpuFlatContinuationUnifiedDescCompact> {
    use super::backward_flat::{
        FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE, TERM_TYPE_C0_ONLY_LINEAR, TERM_TYPE_CONSTANT,
        TERM_TYPE_UNIFIED_LINEAR, TERM_TYPE_UNIFIED_QUADRATIC,
    };
    use std::collections::HashSet;

    let mut compact = Box::new(GpuFlatContinuationUnifiedDescCompact::default());
    let ranges = build_continuation_backing_ranges(storage);
    let term_desc = &plan.term_desc;

    // ----- Source encoding pass -----
    let mut backing_slot: std::collections::HashMap<usize, u8> =
        std::collections::HashMap::with_capacity(GKR_DIM_REDUCING_BASE_SLOTS);
    let mut next_slot: u8 = 0;
    let mut prev_offset_per_slot: [Option<u32>; GKR_DIM_REDUCING_BASE_SLOTS] =
        [None; GKR_DIM_REDUCING_BASE_SLOTS];
    let mut cache_offset_per_slot: [Option<u32>; GKR_DIM_REDUCING_BASE_SLOTS] =
        [None; GKR_DIM_REDUCING_BASE_SLOTS];

    let n = term_desc.num_sources as usize;
    assert!(
        n <= FLAT_CONT_MAX_SOURCES,
        "compact continuation: num_sources {n} exceeds FLAT_CONT_MAX_SOURCES {FLAT_CONT_MAX_SOURCES}",
    );
    compact.num_sources = term_desc.num_sources;

    for i in 0..n {
        let entry = &sources[i];
        let prev_raw = entry.previous_layer_start;
        let cache_raw = entry.this_layer_cache_start as *const u8;
        let first_access = !prev_raw.is_null();

        // Resolve cache pointer (always non-null) to find slot + poly_idx.
        let (base, log2_stride, poly_idx, cache_sub) =
            resolve_continuation_backing_for_pointer(&ranges, cache_raw).unwrap_or_else(|| {
                panic!(
                    "compact continuation: cache pointer {cache_raw:?} (idx {i}) does not fall \
                     within any consolidated folding backing",
                )
            });

        // Assign or look up slot for this backing.
        let key = base as usize;
        let slot = match backing_slot.get(&key) {
            Some(&s) => s,
            None => {
                let s = next_slot;
                assert!(
                    (s as usize) < GKR_DIM_REDUCING_BASE_SLOTS,
                    "compact continuation: distinct backing count exceeds {GKR_DIM_REDUCING_BASE_SLOTS}",
                );
                backing_slot.insert(key, s);
                compact.tables.bases[s as usize] = base;
                compact.tables.log2_stride[s as usize] = log2_stride;
                next_slot += 1;
                s
            }
        };

        // Pin uniform cache offset within this slot (slot's per-poly buffer
        // shape is uniform across all sources mapped to it).
        match cache_offset_per_slot[slot as usize] {
            None => cache_offset_per_slot[slot as usize] = Some(cache_sub),
            Some(p) => assert_eq!(
                p, cache_sub,
                "compact continuation: non-uniform cache_per_poly_offset within slot {slot} (source {i}: {cache_sub}, expected {p})",
            ),
        }

        // If first_access, also resolve prev — must fall in the same backing
        // and same poly_idx, with a different sub-offset.
        if first_access {
            let (p_base, _, p_poly_idx, prev_sub) =
                resolve_continuation_backing_for_pointer(&ranges, prev_raw).unwrap_or_else(|| {
                    panic!(
                        "compact continuation: prev pointer {prev_raw:?} (idx {i}) does not fall \
                             within any consolidated folding backing",
                    )
                });
            assert_eq!(
                p_base as usize, base as usize,
                "compact continuation: prev/cache for source {i} resolve to different backings",
            );
            assert_eq!(
                p_poly_idx, poly_idx,
                "compact continuation: prev/cache for source {i} resolve to different poly_idxs",
            );
            match prev_offset_per_slot[slot as usize] {
                None => prev_offset_per_slot[slot as usize] = Some(prev_sub),
                Some(p) => assert_eq!(
                    p, prev_sub,
                    "compact continuation: non-uniform prev_per_poly_offset within slot {slot} (source {i}: {prev_sub}, expected {p})",
                ),
            }
        }

        let src = pack_source_u16(first_access, slot, poly_idx);
        let cache = pack_cache_u16(slot, poly_idx);
        compact.sources[i] = GpuGKRSourceRecord::new(src, cache);
    }

    for s in 0..GKR_DIM_REDUCING_BASE_SLOTS {
        compact.cache_per_poly_offset[s] = cache_offset_per_slot[s].unwrap_or(0);
        // If no source in this slot had first_access, prev offset is unused
        // and stays 0. Otherwise pin it.
        compact.prev_per_poly_offset[s] = prev_offset_per_slot[s].unwrap_or(0);
    }

    // ----- Term construction + tile/fold pass -----
    const GROUP_SIZE: u16 = FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE as u16;
    let group = |idx: u16| idx / GROUP_SIZE;

    let tile_key = |t: &GpuFlatUnifiedTerm| -> (u16, u16) {
        match t.term_type {
            TERM_TYPE_CONSTANT => (0, 0),
            TERM_TYPE_C0_ONLY_LINEAR | TERM_TYPE_UNIFIED_LINEAR => {
                let g = group(t.source_a);
                (g + 1, g + 1)
            }
            TERM_TYPE_UNIFIED_QUADRATIC => {
                let g0 = group(t.source_a);
                let g1 = group(t.source_b);
                (g0.min(g1) + 1, g0.max(g1) + 1)
            }
            _ => unreachable!(),
        }
    };

    let td = &plan.term_desc;
    let coeff_base_constants = 0u16;
    let coeff_base_c0_only = coeff_base_constants + td.num_constants as u16;
    let coeff_base_quadratic = coeff_base_c0_only + td.num_c0_only_linear as u16;
    let coeff_base_linear = coeff_base_quadratic + td.num_unified_quadratic as u16;

    let total_terms = td.num_constants as usize
        + td.num_c0_only_linear as usize
        + td.num_unified_quadratic as usize
        + td.num_unified_linear as usize;
    assert!(
        total_terms <= FLAT_CONT_UNIFIED_MAX_TERMS,
        "continuation unified terms overflow: {total_terms} > {FLAT_CONT_UNIFIED_MAX_TERMS}",
    );

    let mut terms: Vec<GpuFlatUnifiedTerm> = Vec::with_capacity(total_terms);
    for i in 0..td.num_constants as u16 {
        terms.push(GpuFlatUnifiedTerm {
            source_a: 0,
            source_b: 0,
            term_type: TERM_TYPE_CONSTANT,
            coeff_idx: coeff_base_constants + i,
        });
    }
    for i in 0..term_desc.num_c0_only_linear as u16 {
        terms.push(GpuFlatUnifiedTerm {
            source_a: term_desc.c0_only_linear[i as usize].source_idx,
            source_b: 0,
            term_type: TERM_TYPE_C0_ONLY_LINEAR,
            coeff_idx: coeff_base_c0_only + i,
        });
    }
    for i in 0..term_desc.num_unified_quadratic as u16 {
        let t = term_desc.unified_quadratic[i as usize];
        terms.push(GpuFlatUnifiedTerm {
            source_a: t.source_a,
            source_b: t.source_b,
            term_type: TERM_TYPE_UNIFIED_QUADRATIC,
            coeff_idx: coeff_base_quadratic + i,
        });
    }
    for i in 0..term_desc.num_unified_linear as u16 {
        terms.push(GpuFlatUnifiedTerm {
            source_a: term_desc.unified_linear[i as usize].source_idx,
            source_b: 0,
            term_type: TERM_TYPE_UNIFIED_LINEAR,
            coeff_idx: coeff_base_linear + i,
        });
    }

    terms.sort_by(|a, b| {
        tile_key(a)
            .cmp(&tile_key(b))
            .then(a.term_type.cmp(&b.term_type))
            .then(a.source_a.cmp(&b.source_a))
            .then(a.source_b.cmp(&b.source_b))
    });

    let num_constant_terms = terms
        .iter()
        .take_while(|t| t.term_type == TERM_TYPE_CONSTANT)
        .count();

    let mut tile_boundaries: Vec<(usize, usize)> = Vec::new();
    if num_constant_terms < terms.len() {
        let mut current_key = tile_key(&terms[num_constant_terms]);
        let mut tile_start = num_constant_terms;
        for i in (num_constant_terms + 1)..terms.len() {
            let key = tile_key(&terms[i]);
            if key != current_key {
                tile_boundaries.push((tile_start, i));
                current_key = key;
                tile_start = i;
            }
        }
        tile_boundaries.push((tile_start, terms.len()));
    }

    let num_tiles = tile_boundaries.len();
    assert!(
        num_tiles <= FLAT_CONT_UNIFIED_MAX_TILES,
        "continuation unified tiles overflow: {num_tiles} > {FLAT_CONT_UNIFIED_MAX_TILES}",
    );

    let mut fold_sources: Vec<u16> = Vec::new();
    let mut tile_term_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut tile_fold_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut folded: HashSet<u16> = HashSet::new();

    let needs_folding =
        |src_idx: u16| -> bool { !sources[src_idx as usize].previous_layer_start.is_null() };

    for &(tile_start, tile_end) in &tile_boundaries {
        tile_term_offsets.push(tile_start as u16);
        tile_fold_offsets.push(fold_sources.len() as u16);

        let mut tile_sources: Vec<u16> = Vec::new();
        for t in &terms[tile_start..tile_end] {
            match t.term_type {
                TERM_TYPE_C0_ONLY_LINEAR | TERM_TYPE_UNIFIED_LINEAR => {
                    tile_sources.push(t.source_a);
                }
                TERM_TYPE_UNIFIED_QUADRATIC => {
                    tile_sources.push(t.source_a);
                    tile_sources.push(t.source_b);
                }
                _ => {}
            }
        }
        tile_sources.sort_unstable();
        tile_sources.dedup();

        for src in tile_sources {
            if !folded.contains(&src) && needs_folding(src) {
                fold_sources.push(src);
                folded.insert(src);
            }
        }
    }
    tile_term_offsets.push(terms.len() as u16);
    tile_fold_offsets.push(fold_sources.len() as u16);

    assert!(
        fold_sources.len() <= FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES,
        "continuation unified fold_sources overflow: {} > {FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES}",
        fold_sources.len(),
    );

    compact.terms[..terms.len()].copy_from_slice(&terms);
    compact.num_terms = terms.len() as u32;
    compact.num_constant_terms = num_constant_terms as u32;
    compact.num_tiles = num_tiles as u32;
    compact.tile_term_offsets[..tile_term_offsets.len()].copy_from_slice(&tile_term_offsets);
    compact.tile_fold_offsets[..tile_fold_offsets.len()].copy_from_slice(&tile_fold_offsets);
    compact.fold_sources[..fold_sources.len()].copy_from_slice(&fold_sources);

    compact
}

// ---------------------------------------------------------------------------
// Continuation (rounds ≥ 3) compact kernel declarations + launchers
// ---------------------------------------------------------------------------
//
// Two kernels: non-explicit form
// (`ab_gkr_main_round3_flat_constant_compact_unified_e4_kernel`) and its
// `_explicit_` sibling. The compact descriptor carries prev/cache per-poly
// offsets as descriptor-level u32s; the launch ABI keeps `fold_stride` and
// `next_layer_size` as runtime args.

extern "C" {
    static ab_gkr_round2_challenges: [E4; 3];
    static ab_gkr_main_layer_claim_point: [E4; MAX_MAIN_LAYER_CLAIM_POINT_LEN];
}

pub(super) fn get_main_layer_claim_point_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_main_layer_claim_point is a valid __constant__ symbol
        // defined in main_backward_round1_flat_warp_split.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_main_layer_claim_point as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_main_layer_claim_point");
        p as usize
    });
    ptr as *mut E4
}

fn get_round2_challenges_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_round2_challenges is a valid __constant__ e4[3]
        // symbol defined in main_backward_round2_flat_warp_split.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_round2_challenges as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_round2_challenges");
        p as usize
    });
    ptr as *mut E4
}

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatConstantUnifiedCompact<T>,
    desc: GpuFlatContinuationUnifiedDescCompact,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescCompact,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescCompact,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) trait GpuFlatRound3UnifiedCompactKernelSet: Field {
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
}

impl GpuFlatRound3UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel;
}

pub(super) fn launch_main_round3_flat_constant_unified_compact<
    E: GpuFlatRound3UnifiedCompactKernelSet,
>(
    desc: &GpuFlatContinuationUnifiedDescCompact,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = (acc_size + 31) / 32;
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound3FlatConstantUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        eq_values,
        contributions,
        acc_size,
    );
    let kernel = if explicit_form {
        E::MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT
    } else {
        E::MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT
    };
    GpuGKRMainRound3FlatConstantUnifiedCompactFunction(kernel).launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 1 compact kernel declaration + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDescCompact,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound1UnifiedDescCompact,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) trait GpuFlatRound1UnifiedCompactKernelSet: Field {
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self>;
}

impl GpuFlatRound1UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel;
}

pub(super) fn launch_main_round1_flat_constant_compact_unified_compact<
    E: GpuFlatRound1UnifiedCompactKernelSet,
>(
    desc: &GpuFlatRound1UnifiedDescCompact,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = (acc_size + 31) / 32;
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound1FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 2 compact kernel declaration + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRRound2ChallengesPrelude<T>,
    folding_challenges: *const T,
    staging: *mut T,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_round2_challenges_prelude(
        folding_challenges: *const E4,
        staging: *mut E4,
    )
);

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound2UnifiedDescCompact,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound2UnifiedDescCompact,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) trait GpuFlatRound2UnifiedCompactKernelSet: Field {
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self>;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self>;
}

impl GpuFlatRound2UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self> =
        ab_gkr_round2_challenges_prelude;
}

pub(super) fn launch_main_round2_flat_constant_compact_unified_compact<
    E: GpuFlatRound2UnifiedCompactKernelSet,
>(
    desc: &GpuFlatRound2UnifiedDescCompact,
    folding_challenges: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = (acc_size + 31) / 32;
    let stream = context.get_exec_stream();
    let prelude_config = CudaLaunchConfig::basic(1, 1, stream);
    let prelude_args = GpuGKRRound2ChallengesPreludeArguments::new(
        folding_challenges,
        get_round2_challenges_device_ptr() as *mut E,
    );
    GpuGKRRound2ChallengesPreludeFunction(E::ROUND2_CHALLENGES_PRELUDE)
        .launch(&prelude_config, &prelude_args)?;

    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound2FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Encoder: GpuFlatRound{1,2}UnifiedDesc → compact form
// ---------------------------------------------------------------------------

/// Helper: a unified slot table for round 1/2 encoders. Distinct backing
/// pointers (across `tables.bases`) get assigned slots in first-appearance
/// order. Used for both source backings and cache backings within the same
/// launch.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
