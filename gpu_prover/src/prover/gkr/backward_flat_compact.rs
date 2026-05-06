//! Phase C compact descriptors for the GKR backward main-layer flat path.
//!
//! This module mirrors Phase B's compact dim-reducing path: each per-launch
//! source pointer collapses to a `u16` packed `(virtual?/slot, poly_idx)`
//! reference, with a small per-launch `tables` block (`bases[8]` /
//! `log2_stride[16]`) that the kernel uses to
//! resolve the byte address. The term tables (`c0_bf`, `c0_ext`, `c1_*`,
//! `c1_linear`, etc.) already use u16 source indices and remain unchanged.
//!
//! Phase C scope:
//! - `GpuFlatRound0StaticDescCompact` — round 0 (this round has no folding
//!   cache, so bit 15 of each source u16 doubles as `is_virtual`).
//! - `GpuFlatRound1UnifiedDescCompact`, `GpuFlatRound2UnifiedDescCompact`,
//!   `GpuFlatContinuationUnifiedDescCompact` — landed in subsequent commits.
//!
//! See `/home/rr/.claude/plans/i-would-actually-put-kind-thacker.md` Phase C.

// rustc's dead-code analysis under --lib --tests under-reports usage through
// some of the generic impl chains in `backward.rs` (e.g. `prepare_layer_from_blueprints`
// on `GpuGKRDimensionReducingBackwardState`). Parity tests exercise every
// public function in this module under `--release`. Suppress the false
// positives at module scope.
#![allow(dead_code)]

use super::backward_flat::{
    CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair, GpuFlatUnifiedTerm, FLAT_CONT_MAX_BASE_SOURCES,
    FLAT_CONT_MAX_EXT_SOURCES, FLAT_CONT_MAX_SOURCES, FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES,
    FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES, FLAT_ROUND0_MAX_C0_BF,
    FLAT_ROUND0_MAX_C0_EXT, FLAT_ROUND0_MAX_C1_BF_BF, FLAT_ROUND0_MAX_C1_BF_E4,
    FLAT_ROUND0_MAX_C1_E4_E4, FLAT_ROUND0_MAX_C1_LINEAR, FLAT_ROUND0_MAX_SOURCES,
};
use super::backward_kernels::{
    gkr_dim_reducing_launch_config, pack_cache_u16, pack_source_u16, GpuGKRDimensionReducingTables,
    GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::GpuBaseFieldSourceKind;
use super::GpuGKRStorage;
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::memcpy_to_symbol_from_device_async;
use era_cudart::cuda_kernel_declaration;
use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use field::Field;
use std::ffi::c_void;

/// Hard ceiling: kernel arguments must fit in `cudaLaunchKernelExC`'s 32 KB
/// inline parameter area. Any descriptor whose size exceeds this fails the
/// build (see compile-time assertions below).
pub(super) const KERNEL_ARG_HARD_CEILING_BYTES: usize = 32 * 1024;

/// Soft target: keep descriptors under 16 KB for headroom against future
/// table growth without re-bumping back into H2D territory.
pub(super) const KERNEL_ARG_SOFT_TARGET_BYTES: usize = 16 * 1024;

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

/// Decoded view of a packed flat round-0 source. Used by tests and
/// (eventually) the Rust-side parity assertion against the legacy form.
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

/// Compact mirror of `GpuFlatRound0StaticDesc`. Source pointers collapse to
/// u16 packed references; everything else (term tables) stays bit-identical
/// to the legacy descriptor. Passed by value as `__grid_constant__`.
///
/// Must match CUDA `flat_round0_static_desc_compact` in `flat_backward.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatRound0StaticDescCompact {
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
// parameter area. Phase 0 measured 24,732 B for this descriptor under the
// (8-slot / 4096-polys-per-slot) encoding.
const _: () = {
    assert!(
        std::mem::size_of::<GpuFlatRound0StaticDescCompact>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound0StaticDescCompact exceeds the 32 KB cudaLaunchKernelExC inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// Build plan: compact static desc + recipes (mirror of FlatRound0BuildPlan)
// ---------------------------------------------------------------------------

/// Compact mirror of `FlatRound0BuildPlan`. The recipes vector is identical to
/// the legacy plan's; only the static descriptor changes shape.
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
// byte ranges, then range-map each legacy `*const u8` pointer to the backing
// it falls in. Slot indices are assigned in the order the legacy walk visited
// distinct backings — this preserves the legacy first-appearance dedup keyed
// on the raw pointer (which is what `FlatDescriptionBuilder::source_map` did).

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
            // Tower layers (past artifact range) are not produced by Phase A
            // alone — Phase A2 extends the layout. Round 0 reads only artifact
            // and base-layer polys, so any pointer referencing a missing layer
            // should be unreachable here. Skip safely.
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
// Per-launch metadata cost: 128 B for `tables` (shared with Phase B). Each
// source descriptor is 2 B (down from 16–48 B in the legacy form).

// ---------------------------------------------------------------------------
// Bit-mask constants for rounds 1+ source encoding
// ---------------------------------------------------------------------------

/// Round 1+ ext_source u16 layout (no base/virtual distinction):
///   bit 15      : first_access
///   bits 14..11 : ptr_idx (4 bits, 16 slots)
///   bits 10..0  : poly_idx (11 bits, max 2048; Phase 0 measured max 646)
const CONT_EXT_FIRST_ACCESS_FLAG: u16 = 0x8000;
const CONT_EXT_PTR_IDX_SHIFT: u32 = 11;
const CONT_EXT_PTR_IDX_MASK: u16 = 0xF;
const CONT_EXT_POLY_IDX_MASK: u16 = 0x07FF;

/// Round 1/2 base_source u16 layout:
///   bit 15      : first_access
///   bit 14      : is_virtual
///   bits 13..10 : ptr_idx (4 bits, 16 slots) — real path OR virtual_cache_slot (virtual)
///   bits 9..0   : poly_idx (10 bits, max 1024) — real path OR low 3 bits = source_kind (virtual)
const CONT_BASE_FIRST_ACCESS_FLAG: u16 = 0x8000;
const CONT_BASE_VIRTUAL_FLAG: u16 = 0x4000;
const CONT_BASE_CACHE_VIRTUAL_FLAG: u16 = 0x8000;
const CONT_BASE_PTR_IDX_SHIFT: u32 = 10;
const CONT_BASE_PTR_IDX_MASK: u16 = 0xF;
const CONT_BASE_POLY_IDX_MASK: u16 = 0x03FF;
const CONT_BASE_VIRTUAL_KIND_MASK: u16 = 0x7;

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
pub(super) struct GpuFlatRound1UnifiedDescCompact {
    pub(super) tables: GpuGKRDimensionReducingTables,
    /// `base_poly_len / 2` — uniform across all base sources at this round.
    pub(super) base_layer_half_size: u32,
    /// `fold_stride` for the ext-source pair lookup. Matches the legacy
    /// per-source `next_layer_size`.
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
pub(super) struct GpuFlatRound2UnifiedDescCompact {
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
/// different per-poly buffer sizes (`base_poly_size/2` vs. `poly_size`)
/// — Phase A2-flat-base routes both into per-class consolidated Arcs but
/// the per-poly arithmetic is independent for each.
///
/// The kernel resolves
/// `prev = (E*) tables.bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx]) + prev_per_poly_offset[ptr_idx]`
/// `cache = same + cache_per_poly_offset[ptr_idx]`.
///
/// Must match CUDA `flat_continuation_unified_desc_compact`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatContinuationUnifiedDescCompact {
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

pub(super) trait GpuFlatRound0CompactKernelSet: Field {
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

pub(super) trait GpuFlatRound0ConstantCompactKernelSet: Field {
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
        // Phase A2-flat-base: continuation reads also pull from per-poly
        // base-field folding caches. Those Arcs land here too — same E
        // element type, but the per-poly buffer is half the layout stride
        // (`base_poly_size / 2`). The encoder's stride is the per-poly
        // offset within the consolidated Arc; the layout's `log2_stride`
        // is the natural log2 of that per-poly buffer for this layer.
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
// Two kernels: non-explicit and explicit form (matches the legacy
// `ab_gkr_main_round3_flat_constant_compact_unified_e4_kernel` and its
// `_explicit_` sibling). The compact descriptor takes prev/cache per-poly
// offsets as descriptor-level u32s; the launch ABI matches the legacy form
// so the existing per-step `fold_stride` and `next_layer_size` runtime args
// carry over unchanged.

extern "C" {
    static ab_gkr_round1_challenge: [E4; 1];
    static ab_gkr_round2_challenges: [E4; 3];
    static ab_gkr_round3_challenge: [E4; 1];
}

#[inline]
unsafe fn upload_e4_symbol_from_device<T>(
    symbol: *const c_void,
    src: *const T,
    count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    memcpy_to_symbol_from_device_async(symbol, src, count, stream)
}

era_cudart::cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatConstantUnifiedCompact<T>,
    desc: GpuFlatContinuationUnifiedDescCompact,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(super)
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescCompact,
        fold_stride: u32,
        next_layer_size: u32,
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
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(super) trait GpuFlatRound3UnifiedCompactKernelSet: Field {
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self>;
    unsafe fn upload_round3_challenge(
        folding_challenge: *const Self,
        stream: &CudaStream,
    ) -> CudaResult<()>;
}

impl GpuFlatRound3UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel;
    const MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT:
        GpuGKRMainRound3FlatConstantUnifiedCompactSignature<Self> =
        ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel;
    unsafe fn upload_round3_challenge(
        folding_challenge: *const Self,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        upload_e4_symbol_from_device(
            &ab_gkr_round3_challenge as *const _ as *const c_void,
            folding_challenge,
            1,
            stream,
        )
    }
}

pub(super) fn launch_main_round3_flat_constant_unified_compact<
    E: GpuFlatRound3UnifiedCompactKernelSet,
>(
    desc: &GpuFlatContinuationUnifiedDescCompact,
    folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
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
    // SAFETY: the symbol is a valid __constant__ e4[1] and the source is a
    // device pointer to the current folding challenge, ordered on exec_stream.
    unsafe { E::upload_round3_challenge(folding_challenge, stream)? };
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound3FlatConstantUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
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

pub(super) trait GpuFlatRound1UnifiedCompactKernelSet: Field {
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self>;
    unsafe fn upload_round1_challenge(
        folding_challenge: *const Self,
        stream: &CudaStream,
    ) -> CudaResult<()>;
}

impl GpuFlatRound1UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound1FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel;
    unsafe fn upload_round1_challenge(
        folding_challenge: *const Self,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        upload_e4_symbol_from_device(
            &ab_gkr_round1_challenge as *const _ as *const c_void,
            folding_challenge,
            1,
            stream,
        )
    }
}

pub(super) fn launch_main_round1_flat_constant_compact_unified_compact<
    E: GpuFlatRound1UnifiedCompactKernelSet,
>(
    desc: &GpuFlatRound1UnifiedDescCompact,
    folding_challenge: *const E,
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
    // SAFETY: the symbol is a valid __constant__ e4[1] and the source is a
    // device pointer to the current folding challenge, ordered on exec_stream.
    unsafe { E::upload_round1_challenge(folding_challenge, stream)? };
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

pub(super) trait GpuFlatRound2UnifiedCompactKernelSet: Field {
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self>;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self>;
    unsafe fn upload_round2_challenges(staging: *const Self, stream: &CudaStream)
        -> CudaResult<()>;
}

impl GpuFlatRound2UnifiedCompactKernelSet for E4 {
    const MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT:
        GpuGKRMainRound2FlatConstantCompactUnifiedCompactSignature<Self> =
        ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel;
    const ROUND2_CHALLENGES_PRELUDE: GpuGKRRound2ChallengesPreludeSignature<Self> =
        ab_gkr_round2_challenges_prelude;
    unsafe fn upload_round2_challenges(
        staging: *const Self,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        upload_e4_symbol_from_device(
            &ab_gkr_round2_challenges as *const _ as *const c_void,
            staging,
            3,
            stream,
        )
    }
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
    let mut staging = context.alloc(3, AllocationPlacement::BestFit)?;
    let prelude_config = CudaLaunchConfig::basic(1, 1, stream);
    let prelude_args =
        GpuGKRRound2ChallengesPreludeArguments::new(folding_challenges, staging.as_mut_ptr());
    GpuGKRRound2ChallengesPreludeFunction(E::ROUND2_CHALLENGES_PRELUDE)
        .launch(&prelude_config, &prelude_args)?;
    // SAFETY: the symbol is a valid __constant__ e4[3] and `staging` contains
    // [first, second, first * second], produced by the preceding exec-stream kernel.
    unsafe { E::upload_round2_challenges(staging.as_ptr(), stream)? };

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
// Encoder: legacy GpuFlatRound{1,2}UnifiedDesc → compact form
// ---------------------------------------------------------------------------

/// Helper: a unified slot table for round 1/2 encoders. Distinct backing
/// pointers (across `tables.bases`) get assigned slots in first-appearance
/// order. Used for both source backings and cache backings within the same
/// launch.
struct SlotTable {
    /// `backing_base_addr -> slot_idx`.
    map: std::collections::HashMap<usize, u8>,
    next_slot: u8,
}

impl SlotTable {
    fn new() -> Self {
        Self {
            map: std::collections::HashMap::with_capacity(GKR_DIM_REDUCING_BASE_SLOTS),
            next_slot: 0,
        }
    }

    fn assign(
        &mut self,
        tables: &mut GpuGKRDimensionReducingTables,
        base: *const u8,
        log2_stride: u32,
    ) -> u8 {
        let key = base as usize;
        if let Some(&s) = self.map.get(&key) {
            // Verify stride consistency across re-assignments.
            debug_assert_eq!(
                tables.log2_stride[s as usize], log2_stride,
                "compact round 1/2: backing {base:?} re-assigned with mismatched log2_stride ({} vs {})",
                tables.log2_stride[s as usize], log2_stride,
            );
            return s;
        }
        let s = self.next_slot;
        assert!(
            (s as usize) < GKR_DIM_REDUCING_BASE_SLOTS,
            "compact round 1/2: distinct backing count exceeds {GKR_DIM_REDUCING_BASE_SLOTS}",
        );
        self.map.insert(key, s);
        tables.bases[s as usize] = base;
        tables.log2_stride[s as usize] = log2_stride;
        self.next_slot += 1;
        s
    }
}

/// Resolve a base-input pointer at round 1/2: sub-offset within the per-poly
/// slot must be 0 (round 0/1/2 base inputs are full-poly reads). Returns
/// `(backing_base, log2_stride, poly_idx)`.
fn resolve_source_pointer(ranges: &[BackingRange], ptr: *const u8) -> (*const u8, u32, u16) {
    let (base, log2_stride, poly_idx) = resolve_backing_for_pointer(ranges, ptr).unwrap_or_else(
        || panic!("compact round 1/2: source pointer {ptr:?} does not fall within any consolidated source backing"),
    );
    (base, log2_stride, poly_idx)
}

/// Resolve a cache-write pointer at round 1: sub-offset within the per-poly
/// cache buffer must be 0 (round 1 always writes to position 0 in the cache).
/// Returns `(cache_base, cache_log2_stride, poly_idx)`.
fn resolve_round1_cache_pointer<E: Field>(
    cache_ranges: &[ContinuationBackingRange],
    ptr: *const u8,
) -> (*const u8, u32, u16) {
    let (base, log2_stride, poly_idx, sub_offset) =
        resolve_continuation_backing_for_pointer(cache_ranges, ptr).unwrap_or_else(|| {
            panic!(
                "compact round 1: cache pointer {ptr:?} does not fall within any consolidated cache backing"
            )
        });
    assert_eq!(
        sub_offset, 0,
        "compact round 1: cache pointer {ptr:?} has non-zero sub_offset {sub_offset}",
    );
    let _ = std::marker::PhantomData::<E>;
    (base, log2_stride, poly_idx)
}

/// Build a compact round-1 unified descriptor directly from the round-1
/// fused-source data, the continuation plan, and storage. Source pointers
/// resolve to compact `(slot, poly_idx)` records and term/tile/fold
/// metadata builds inline. Term arrays come from `plan.term_desc` with
/// `round1_fused.idx_remap` applied per source-index reference.
///
/// Each dual source record carries the source slot/poly_idx and cache
/// slot/poly_idx explicitly.
pub(super) fn build_flat_round1_unified_desc_compact<E: Field>(
    round1_fused: &super::backward_flat::Round1FusedSources,
    plan: &super::backward_flat::FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Box<GpuFlatRound1UnifiedDescCompact> {
    use super::backward_flat::{
        FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE, TERM_TYPE_C0_ONLY_LINEAR,
        TERM_TYPE_CONSTANT, TERM_TYPE_UNIFIED_LINEAR, TERM_TYPE_UNIFIED_QUADRATIC,
    };
    use std::collections::HashSet;

    let mut compact = Box::new(GpuFlatRound1UnifiedDescCompact::default());
    let source_ranges = build_backing_ranges(storage);
    let cache_ranges = build_continuation_backing_ranges(storage);

    let mut slots = SlotTable::new();

    let nb = round1_fused.num_base_sources as usize;
    let ne = round1_fused.num_ext_sources as usize;
    assert!(
        nb <= FLAT_CONT_MAX_BASE_SOURCES,
        "compact round 1: num_base_sources {nb} exceeds {FLAT_CONT_MAX_BASE_SOURCES}",
    );
    assert!(
        ne <= FLAT_CONT_MAX_EXT_SOURCES,
        "compact round 1: num_ext_sources {ne} exceeds {FLAT_CONT_MAX_EXT_SOURCES}",
    );
    compact.num_base_sources = round1_fused.num_base_sources;
    compact.num_ext_sources = round1_fused.num_ext_sources;

    // base_layer_half_size and next_layer_size are uniform across all base
    // entries — pin from the first one. Ext sources also use next_layer_size
    // implicitly (it's the second-fold stride at sumcheck step 1).
    let mut layer_metadata: Option<(u32, u32)> = None;

    for i in 0..nb {
        let entry = &round1_fused.base_sources[i];
        let half = entry.base_layer_half_size as u32;
        let next = entry.next_layer_size as u32;
        match layer_metadata {
            None => layer_metadata = Some((half, next)),
            Some((h, n)) => {
                assert_eq!(
                    h, half,
                    "compact round 1: non-uniform base_layer_half_size at base_source[{i}]"
                );
                assert_eq!(
                    n, next,
                    "compact round 1: non-uniform next_layer_size at base_source[{i}]"
                );
            }
        }
        let cache_raw = entry.this_layer_cache_start as *const u8;
        let (cache_base, cache_log2, cache_poly_idx) =
            resolve_round1_cache_pointer::<E>(&cache_ranges, cache_raw);
        let cache_slot = slots.assign(&mut compact.tables, cache_base, cache_log2);
        let cache = pack_cache_u16(cache_slot, cache_poly_idx);
        match entry.source_kind {
            GpuBaseFieldSourceKind::Real => {
                let src_raw = entry.base_input_start;
                let (src_base, src_log2, src_poly_idx) =
                    resolve_source_pointer(&source_ranges, src_raw);
                let src_slot = slots.assign(&mut compact.tables, src_base, src_log2);
                let src = pack_source_u16(entry.first_access, src_slot, src_poly_idx);
                compact.base_sources[i] = GpuGKRSourceRecord::new(src, cache);
            }
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
            | GpuBaseFieldSourceKind::VirtualRangeCheckTimestamp
            | GpuBaseFieldSourceKind::VirtualInitsAndTeardownsLow
            | GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh => {
                let kind = entry.source_kind as u8;
                let src = if entry.first_access {
                    CONT_BASE_FIRST_ACCESS_FLAG
                } else {
                    0
                } | (kind as u16 & CONT_BASE_VIRTUAL_KIND_MASK);
                compact.base_sources[i] =
                    GpuGKRSourceRecord::new(src, cache | CONT_BASE_CACHE_VIRTUAL_FLAG);
            }
            GpuBaseFieldSourceKind::Empty => {
                panic!("compact round 1: unexpected Empty source_kind at base_source[{i}]")
            }
        }
    }

    for i in 0..ne {
        let entry = &round1_fused.ext_sources[i];
        let prev_raw = entry.previous_layer_start;
        let cache_raw = entry.this_layer_cache_start as *const u8;
        let first_access = !prev_raw.is_null();
        let (cache_base, cache_log2, cache_poly_idx) =
            resolve_round1_cache_pointer::<E>(&cache_ranges, cache_raw);
        let cache_slot = slots.assign(&mut compact.tables, cache_base, cache_log2);
        let cache = pack_cache_u16(cache_slot, cache_poly_idx);
        let (src_slot, src_poly_idx) = if first_access {
            // Round 1 ext sources at first_access read from the consolidated
            // ext source backing (`ext_class_backings[class]`). Subsequent
            // accesses at round 1 (re-reads of the same source within a
            // launch) point at the cache; treat those by reusing the cache
            // slot.
            let (src_base, src_log2, src_poly_idx) =
                resolve_source_pointer(&source_ranges, prev_raw);
            let src_slot = slots.assign(&mut compact.tables, src_base, src_log2);
            (src_slot, src_poly_idx)
        } else {
            // The kernel reads from cache directly; re-encode using the cache
            // slot as the source slot; no separate source backing is needed
            // for the re-read.
            (cache_slot, cache_poly_idx)
        };
        let src = pack_source_u16(first_access, src_slot, src_poly_idx);
        compact.ext_sources[i] = GpuGKRSourceRecord::new(src, cache);
    }

    // For ext-only round 1 (no base sources), `base_layer_half_size` and
    // `next_layer_size` descriptor fields are unused — the kernel takes both
    // sizes via runtime args (`fold_stride`, `next_layer_size`) and never
    // reads `desc.base_layer_half_size` because no base sources are folded.
    let (half, next) = layer_metadata.unwrap_or((0, 0));
    compact.base_layer_half_size = half;
    compact.next_layer_size = next;

    // ----- Term construction + tile/fold pass -----
    const GROUP_SIZE: u16 = FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE as u16;
    let group = |idx: u16| (idx & !FLAT_CONT_EXT_SOURCE_BIT) / GROUP_SIZE;

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
        "round1 unified terms overflow: {total_terms} > {FLAT_CONT_UNIFIED_MAX_TERMS}",
    );

    // Apply round1 idx_remap (continuation source_table_idx → tagged round1
    // index, with `FLAT_CONT_EXT_SOURCE_BIT` set for ext entries) inline as
    // we materialize compact term records.
    let remap = &round1_fused.idx_remap;
    debug_assert_eq!(
        remap.len(),
        td.num_sources as usize,
        "compact round 1: idx_remap length mismatch with continuation plan",
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
    for i in 0..td.num_c0_only_linear as u16 {
        let raw = td.c0_only_linear[i as usize].source_idx;
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[raw as usize],
            source_b: 0,
            term_type: TERM_TYPE_C0_ONLY_LINEAR,
            coeff_idx: coeff_base_c0_only + i,
        });
    }
    for i in 0..td.num_unified_quadratic as u16 {
        let t = td.unified_quadratic[i as usize];
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[t.source_a as usize],
            source_b: remap[t.source_b as usize],
            term_type: TERM_TYPE_UNIFIED_QUADRATIC,
            coeff_idx: coeff_base_quadratic + i,
        });
    }
    for i in 0..td.num_unified_linear as u16 {
        let raw = td.unified_linear[i as usize].source_idx;
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[raw as usize],
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
        "round1 unified tiles overflow: {num_tiles} > {FLAT_CONT_UNIFIED_MAX_TILES}",
    );

    let mut fold_sources: Vec<u16> = Vec::new();
    let mut tile_term_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut tile_fold_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut folded: HashSet<u16> = HashSet::new();

    let needs_folding = |src_idx: u16| -> bool {
        if src_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
            let raw = (src_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
            !round1_fused.ext_sources[raw].previous_layer_start.is_null()
        } else {
            round1_fused.base_sources[src_idx as usize].first_access
        }
    };

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
        "round1 unified fold_sources overflow: {} > {FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES}",
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

/// Resolve a round-2 cache pointer. For base sources at round 2, the legacy
/// `this_layer_cache_start = buffer.initial_pointer()` (sub_offset=0), same
/// as round 1. For ext sources at round 2 (sumcheck_step=2), the legacy
/// `pointer_for_sumcheck_continuation(2)` returns `(buffer_start, buffer_start
/// + size_after_one_fold)` — both within the consolidated ext-folding Arc.
/// `previous_layer_start` is at sub_offset=0; `this_layer_cache_start` is at
/// sub_offset=`size_after_one_fold`. We don't validate sub_offset here
/// (caller-specific).
fn resolve_round2_cache_pointer<E: Field>(
    cache_ranges: &[ContinuationBackingRange],
    ptr: *const u8,
) -> (*const u8, u32, u16, u32) {
    let _ = std::marker::PhantomData::<E>;
    resolve_continuation_backing_for_pointer(cache_ranges, ptr).unwrap_or_else(|| {
        panic!(
            "compact round 2: cache pointer {ptr:?} does not fall within any consolidated cache backing"
        )
    })
}

/// Build a compact round-2 unified descriptor directly from the static round-2
/// desc, the continuation plan, and storage. Fuses
/// `build_round2_tiled_desc + convert_flat_round2_unified_legacy_to_compact`
/// into a single pass.
///
/// Mirrors the round-1 fused builder with three differences:
/// 1. Base entries carry an extra `base_quarter_size` (= base_poly_size / 4)
///    that hoists into a descriptor-level u32.
/// 2. Round 2 base `this_layer_cache_start = buffer.initial_pointer()` —
///    same shape as round 1, sub_offset must be 0.
/// 3. Round 2 ext `previous_layer_start` and `this_layer_cache_start` BOTH
///    live in `intermediate_folding_consolidated`. The builder treats the
///    ext slot like continuation: source and cache resolve to the same Arc
///    with different sub_offsets. The kernel computes both offsets via
///    per-step arithmetic, mirroring the continuation path.
pub(super) fn build_flat_round2_unified_desc_compact<E: Field>(
    round2_fused: &super::backward_flat::Round2FusedSources,
    plan: &super::backward_flat::FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Box<GpuFlatRound2UnifiedDescCompact> {
    use super::backward_flat::{
        FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE, TERM_TYPE_C0_ONLY_LINEAR,
        TERM_TYPE_CONSTANT, TERM_TYPE_UNIFIED_LINEAR, TERM_TYPE_UNIFIED_QUADRATIC,
    };
    use std::collections::HashSet;

    let mut compact = Box::new(GpuFlatRound2UnifiedDescCompact::default());
    let source_ranges = build_backing_ranges(storage);
    let cache_ranges = build_continuation_backing_ranges(storage);

    let mut slots = SlotTable::new();

    let nb = round2_fused.num_base_sources as usize;
    let ne = round2_fused.num_ext_sources as usize;
    assert!(
        nb <= FLAT_CONT_MAX_BASE_SOURCES,
        "compact round 2: num_base_sources {nb} exceeds {FLAT_CONT_MAX_BASE_SOURCES}",
    );
    assert!(
        ne <= FLAT_CONT_MAX_EXT_SOURCES,
        "compact round 2: num_ext_sources {ne} exceeds {FLAT_CONT_MAX_EXT_SOURCES}",
    );
    compact.num_base_sources = round2_fused.num_base_sources;
    compact.num_ext_sources = round2_fused.num_ext_sources;

    let mut layer_metadata: Option<(u32, u32, u32)> = None;

    for i in 0..nb {
        let entry = &round2_fused.base_sources[i];
        let half = entry.base_layer_half_size as u32;
        let quarter = entry.base_quarter_size as u32;
        let next = entry.next_layer_size as u32;
        match layer_metadata {
            None => layer_metadata = Some((half, quarter, next)),
            Some((h, q, n)) => {
                assert_eq!(
                    h, half,
                    "compact round 2: non-uniform half at base_source[{i}]"
                );
                assert_eq!(
                    q, quarter,
                    "compact round 2: non-uniform quarter at base_source[{i}]"
                );
                assert_eq!(
                    n, next,
                    "compact round 2: non-uniform next at base_source[{i}]"
                );
            }
        }
        let cache_raw = entry.this_layer_cache_start as *const u8;
        let (cache_base, cache_log2, cache_poly_idx, cache_sub) =
            resolve_round2_cache_pointer::<E>(&cache_ranges, cache_raw);
        assert_eq!(
            cache_sub, 0,
            "compact round 2: base cache sub_offset must be 0, got {cache_sub} at base_source[{i}]",
        );
        let cache_slot = slots.assign(&mut compact.tables, cache_base, cache_log2);
        let cache = pack_cache_u16(cache_slot, cache_poly_idx);
        match entry.source_kind {
            GpuBaseFieldSourceKind::Real => {
                let src_raw = entry.base_input_start;
                let (src_base, src_log2, src_poly_idx) =
                    resolve_source_pointer(&source_ranges, src_raw);
                let src_slot = slots.assign(&mut compact.tables, src_base, src_log2);
                let src = pack_source_u16(entry.first_access, src_slot, src_poly_idx);
                compact.base_sources[i] = GpuGKRSourceRecord::new(src, cache);
            }
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
            | GpuBaseFieldSourceKind::VirtualRangeCheckTimestamp
            | GpuBaseFieldSourceKind::VirtualInitsAndTeardownsLow
            | GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh => {
                let kind = entry.source_kind as u8;
                let src = if entry.first_access {
                    CONT_BASE_FIRST_ACCESS_FLAG
                } else {
                    0
                } | (kind as u16 & CONT_BASE_VIRTUAL_KIND_MASK);
                compact.base_sources[i] =
                    GpuGKRSourceRecord::new(src, cache | CONT_BASE_CACHE_VIRTUAL_FLAG);
            }
            GpuBaseFieldSourceKind::Empty => {
                panic!("compact round 2: unexpected Empty source_kind at base_source[{i}]")
            }
        }
    }

    for i in 0..ne {
        let entry = &round2_fused.ext_sources[i];
        let prev_raw = entry.previous_layer_start;
        let cache_raw = entry.this_layer_cache_start as *const u8;
        let first_access = !prev_raw.is_null();
        let (cache_base, cache_log2, cache_poly_idx, _cache_sub) =
            resolve_round2_cache_pointer::<E>(&cache_ranges, cache_raw);
        let cache_slot = slots.assign(&mut compact.tables, cache_base, cache_log2);
        let cache = pack_cache_u16(cache_slot, cache_poly_idx);
        if first_access {
            let (prev_base, prev_log2, prev_poly_idx, _prev_sub) =
                resolve_round2_cache_pointer::<E>(&cache_ranges, prev_raw);
            assert_eq!(
                prev_base as usize, cache_base as usize,
                "compact round 2: ext prev/cache resolve to different backings at ext_source[{i}]"
            );
            assert_eq!(
                prev_poly_idx, cache_poly_idx,
                "compact round 2: ext prev/cache poly_idx mismatch at ext_source[{i}]"
            );
            let _ = prev_log2;
        }
        let src = pack_source_u16(first_access, cache_slot, cache_poly_idx);
        compact.ext_sources[i] = GpuGKRSourceRecord::new(src, cache);
    }

    // For ext-only round 2 (no base sources), the base size fields are
    // unused — the kernel takes both sizes via runtime args and never
    // reads `desc.base_layer_half_size` / `desc.base_quarter_size`.
    let (half, quarter, next) = layer_metadata.unwrap_or((0, 0, 0));
    compact.base_layer_half_size = half;
    compact.base_quarter_size = quarter;
    compact.next_layer_size = next;

    // ----- Term construction + tile/fold pass (mirrors round 1) -----
    const GROUP_SIZE: u16 = FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE as u16;
    let group = |idx: u16| (idx & !FLAT_CONT_EXT_SOURCE_BIT) / GROUP_SIZE;

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
        "round2 unified terms overflow: {total_terms} > {FLAT_CONT_UNIFIED_MAX_TERMS}",
    );

    // Apply round2 idx_remap (continuation source_table_idx → tagged round2
    // index, with `FLAT_CONT_EXT_SOURCE_BIT` set for ext entries) inline as
    // we materialize compact term records.
    let remap = &round2_fused.idx_remap;
    debug_assert_eq!(
        remap.len(),
        td.num_sources as usize,
        "compact round 2: idx_remap length mismatch with continuation plan",
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
    for i in 0..td.num_c0_only_linear as u16 {
        let raw = td.c0_only_linear[i as usize].source_idx;
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[raw as usize],
            source_b: 0,
            term_type: TERM_TYPE_C0_ONLY_LINEAR,
            coeff_idx: coeff_base_c0_only + i,
        });
    }
    for i in 0..td.num_unified_quadratic as u16 {
        let t = td.unified_quadratic[i as usize];
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[t.source_a as usize],
            source_b: remap[t.source_b as usize],
            term_type: TERM_TYPE_UNIFIED_QUADRATIC,
            coeff_idx: coeff_base_quadratic + i,
        });
    }
    for i in 0..td.num_unified_linear as u16 {
        let raw = td.unified_linear[i as usize].source_idx;
        terms.push(GpuFlatUnifiedTerm {
            source_a: remap[raw as usize],
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
        "round2 unified tiles overflow: {num_tiles} > {FLAT_CONT_UNIFIED_MAX_TILES}",
    );

    let mut fold_sources: Vec<u16> = Vec::new();
    let mut tile_term_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut tile_fold_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut folded: HashSet<u16> = HashSet::new();

    let needs_folding = |src_idx: u16| -> bool {
        if src_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
            let raw = (src_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
            !round2_fused.ext_sources[raw].previous_layer_start.is_null()
        } else {
            round2_fused.base_sources[src_idx as usize].first_access
        }
    };

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
        "round2 unified fold_sources overflow: {} > {FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES}",
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
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_unpack_real_round_trip() {
        for slot in 0..GKR_DIM_REDUCING_BASE_SLOTS as u8 {
            for poly_idx in [0u16, 1, 7, 64, 645, 0x07FF] {
                let packed = pack_flat_round0_source_real(slot, poly_idx);
                assert_eq!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
                let unpacked = unpack_flat_round0_source(packed);
                assert_eq!(
                    unpacked,
                    UnpackedFlatRound0Source::Real { slot, poly_idx },
                    "round-trip failed for slot={slot} poly_idx={poly_idx} packed={packed:#06x}",
                );
            }
        }
    }

    #[test]
    fn pack_unpack_virtual_round_trip() {
        for kind in 0u8..=7 {
            let packed = pack_flat_round0_source_virtual(kind);
            assert_ne!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
            assert_eq!(
                unpack_flat_round0_source(packed),
                UnpackedFlatRound0Source::Virtual { kind },
            );
        }
    }

    #[test]
    fn pack_real_uses_lower_15_bits_only() {
        // Bit 15 must be reserved for the virtual flag. With 4-bit slot and
        // 11-bit poly_idx, max real-pack value is 0x7FFF.
        let packed = pack_flat_round0_source_real(0xF, 0x07FF);
        assert_eq!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
        assert_eq!(packed, 0x7FFF);
    }

    #[test]
    fn descriptor_size_matches_phase0_audit() {
        // Anchored to the audit's projected post-compaction size so any
        // future field addition or slot-count change that diverges from the
        // audit projection is caught here.
        let size = std::mem::size_of::<GpuFlatRound0StaticDescCompact>();
        assert!(
            size <= KERNEL_ARG_HARD_CEILING_BYTES,
            "descriptor size {size} exceeds 32 KB hard ceiling",
        );
        let projected = super::super::gkr_address_audit::projected_post_compaction_sizes()
            .flat_round0_static_desc;
        assert_eq!(
            size, projected,
            "actual sizeof ({size}) differs from audit projection ({projected})",
        );
    }

    #[test]
    fn round1_descriptor_size_under_soft_target() {
        let size = std::mem::size_of::<GpuFlatRound1UnifiedDescCompact>();
        assert!(
            size <= KERNEL_ARG_HARD_CEILING_BYTES,
            "round 1 compact desc size {size} > 32 KB ceiling",
        );
        assert!(
            size <= KERNEL_ARG_SOFT_TARGET_BYTES,
            "round 1 compact desc size {size} > 16 KB soft target — \
             investigate before continuing Phase C round 1",
        );
    }

    #[test]
    fn round2_descriptor_size_under_soft_target() {
        let size = std::mem::size_of::<GpuFlatRound2UnifiedDescCompact>();
        assert!(size <= KERNEL_ARG_HARD_CEILING_BYTES);
        assert!(size <= KERNEL_ARG_SOFT_TARGET_BYTES);
    }

    #[test]
    fn continuation_descriptor_size_under_soft_target() {
        let size = std::mem::size_of::<GpuFlatContinuationUnifiedDescCompact>();
        assert!(size <= KERNEL_ARG_HARD_CEILING_BYTES);
        assert!(size <= KERNEL_ARG_SOFT_TARGET_BYTES);
    }

    #[test]
    fn cont_ext_pack_unpack_round_trip() {
        for first in [false, true] {
            for slot in 0u8..=0xF {
                for poly_idx in [0u16, 1, 7, 64, 645, 0x07FF] {
                    let packed = pack_cont_ext_source(first, slot, poly_idx);
                    let unpacked = unpack_cont_ext_source(packed);
                    assert_eq!(unpacked.first_access, first);
                    assert_eq!(unpacked.slot, slot);
                    assert_eq!(unpacked.poly_idx, poly_idx);
                }
            }
        }
    }

    #[test]
    fn cont_base_real_pack_unpack_round_trip() {
        for first in [false, true] {
            for slot in 0u8..=0xF {
                for poly_idx in [0u16, 1, 7, 64, 645, 0x03FF] {
                    let packed = pack_cont_base_source_real(first, slot, poly_idx);
                    match unpack_cont_base_source(packed) {
                        UnpackedContBaseSource::Real {
                            first_access,
                            slot: s,
                            poly_idx: p,
                        } => {
                            assert_eq!(first_access, first);
                            assert_eq!(s, slot);
                            assert_eq!(p, poly_idx);
                        }
                        UnpackedContBaseSource::Virtual { .. } => {
                            panic!("real source decoded as virtual: {packed:#06x}")
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn cont_base_virtual_pack_unpack_round_trip() {
        for first in [false, true] {
            for cache_slot in 0u8..=0xF {
                for kind in 0u8..=7 {
                    let packed = pack_cont_base_source_virtual(first, cache_slot, kind);
                    match unpack_cont_base_source(packed) {
                        UnpackedContBaseSource::Virtual {
                            first_access,
                            cache_slot: cs,
                            kind: k,
                        } => {
                            assert_eq!(first_access, first);
                            assert_eq!(cs, cache_slot);
                            assert_eq!(k, kind);
                        }
                        UnpackedContBaseSource::Real { .. } => {
                            panic!("virtual source decoded as real: {packed:#06x}")
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn descriptor_default_zeroes_counts() {
        let desc = GpuFlatRound0StaticDescCompact::default();
        assert_eq!(desc.num_sources, 0);
        assert_eq!(desc.num_c0_bf, 0);
        assert_eq!(desc.num_c0_ext, 0);
        assert_eq!(desc.num_c1_bf_bf, 0);
        assert_eq!(desc.num_c1_e4_e4, 0);
        assert_eq!(desc.num_c1_bf_e4, 0);
        assert_eq!(desc.num_c1_linear, 0);
        // Tables default to all-null bases and zero strides.
        for slot in 0..GKR_DIM_REDUCING_BASE_SLOTS {
            assert!(desc.tables.bases[slot].is_null());
            assert_eq!(desc.tables.log2_stride[slot], 0);
        }
    }
}
