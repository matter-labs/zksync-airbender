//! Compact round-0 static descriptor + storage backing reverse-map.

use super::super::super::GpuGKRStorage;
use super::super::flat::{
    CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair, FLAT_ROUND0_MAX_C0_BF, FLAT_ROUND0_MAX_C0_EXT,
    FLAT_ROUND0_MAX_C1_BF_BF, FLAT_ROUND0_MAX_C1_BF_E4, FLAT_ROUND0_MAX_C1_E4_E4,
    FLAT_ROUND0_MAX_C1_LINEAR, FLAT_ROUND0_MAX_SOURCES,
};
use super::super::kernels::{GpuGKRDimensionReducingTables, GpuGKRSourceRecord};
use super::encoding::FLAT_SOURCE_POLY_IDX_MASK;
use super::kernel_limits::KERNEL_ARG_HARD_CEILING_BYTES;
use crate::primitives::field::BF;
use crate::upstream::Field;

// ---------------------------------------------------------------------------
// GpuFlatRound0StaticDesc
// ---------------------------------------------------------------------------

/// Compact flat round-0 static descriptor. Source pointers are u16 packed
/// references; term tables stay as in the verbose descriptor. Passed by
/// value as `__grid_constant__`.
///
/// Must match CUDA `flat_round0_static_desc_compact` in `flat_backward.cuh`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatRound0StaticDesc {
    pub(crate) tables: GpuGKRDimensionReducingTables,

    pub(crate) sources: [GpuGKRSourceRecord; FLAT_ROUND0_MAX_SOURCES],
    pub(crate) num_sources: u32,

    pub(crate) c0_bf: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_BF],
    pub(crate) num_c0_bf: u32,
    pub(crate) c0_ext: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_EXT],
    pub(crate) num_c0_ext: u32,

    pub(crate) c1_bf_bf: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_BF],
    pub(crate) num_c1_bf_bf: u32,
    pub(crate) c1_e4_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_E4_E4],
    pub(crate) num_c1_e4_e4: u32,
    pub(crate) c1_bf_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_E4],
    pub(crate) num_c1_bf_e4: u32,

    pub(crate) c1_linear: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C1_LINEAR],
    pub(crate) num_c1_linear: u32,
}

unsafe impl Send for GpuFlatRound0StaticDesc {}
unsafe impl Sync for GpuFlatRound0StaticDesc {}

impl Default for GpuFlatRound0StaticDesc {
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
        std::mem::size_of::<GpuFlatRound0StaticDesc>() <= KERNEL_ARG_HARD_CEILING_BYTES,
        "GpuFlatRound0StaticDesc exceeds the 32 KB cudaLaunchKernelExC inline ceiling",
    );
};

// ---------------------------------------------------------------------------
// Build plan: compact static desc + recipes (mirror of FlatRound0BuildPlan)
// ---------------------------------------------------------------------------

/// Compact mirror of `FlatRound0BuildPlan` with the compact static descriptor.
pub(crate) struct FlatRound0BuildPlan<E> {
    pub(crate) static_desc: Box<GpuFlatRound0StaticDesc>,
    pub(crate) recipes: Vec<CoefficientRecipe<E>>,
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
pub(crate) struct BackingRange {
    /// Backing base (cast to `*const u8` for ABI uniformity with `tables.bases`).
    pub(crate) base: *const u8,
    /// `start_byte..end_byte` half-open range of valid pointer addresses
    /// inside this backing.
    pub(crate) start_byte: usize,
    pub(crate) end_byte: usize,
    /// Element size of the backing (4 for base-field, 16 for ext-field on E4).
    pub(crate) elem_bytes: usize,
    /// Per-poly stride in elements (= layer's `log2_stride`).
    pub(crate) log2_stride: u32,
}

pub(crate) fn build_backing_ranges<E: Field>(storage: &GpuGKRStorage<BF, E>) -> Vec<BackingRange> {
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
pub(crate) fn resolve_backing_for_pointer(
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
