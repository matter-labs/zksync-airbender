use super::super::{CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair};
use crate::primitives::field::BF;
use crate::upstream::Field;

pub(crate) const FLAT_CONT_MAX_SOURCES: usize = 512;
pub(crate) const FLAT_CONT_MAX_C0_ONLY_LINEAR: usize = 640;
pub(crate) const FLAT_CONT_MAX_UNIFIED_QUADRATIC: usize = 4608;
pub(crate) const FLAT_CONT_MAX_UNIFIED_LINEAR: usize = 128;
pub(crate) const FLAT_CONT_MAX_CONSTANT: usize = 64;

// Round 1/2 mixed source limits
pub(crate) const FLAT_CONT_MAX_BASE_SOURCES: usize = 128;
pub(crate) const FLAT_CONT_MAX_EXT_SOURCES: usize = 384;
pub(crate) const FLAT_CONT_EXT_SOURCE_BIT: u16 = 0x8000;

// Unified tiled kernel constants
pub(crate) const FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE: usize = 4;
#[allow(dead_code)]
pub(crate) const FLAT_CONT_UNIFIED_MAX_GRID_DIM: usize =
    (FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES) / FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE;
pub(crate) const FLAT_CONT_UNIFIED_MAX_TERMS: usize = 1024;
// Sparse: only non-empty tiles stored. Each tile has ≥1 term, so max tiles ≤ max terms.
pub(crate) const FLAT_CONT_UNIFIED_MAX_TILES: usize = FLAT_CONT_UNIFIED_MAX_TERMS;
pub(crate) const FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES: usize =
    FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES;

// ---------------------------------------------------------------------------
// Static description types (mirror CUDA structs)
// ---------------------------------------------------------------------------

/// Compact source descriptor for continuing sources.
/// `previous_layer_start == null` encodes `!first_access` (read from cache).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatContinuingSourceEntry {
    pub(crate) previous_layer_start: *const u8,
    pub(crate) this_layer_cache_start: *mut u8,
}

unsafe impl Send for GpuFlatContinuingSourceEntry {}
unsafe impl Sync for GpuFlatContinuingSourceEntry {}

impl Default for GpuFlatContinuingSourceEntry {
    fn default() -> Self {
        Self {
            previous_layer_start: std::ptr::null(),
            this_layer_cache_start: std::ptr::null_mut(),
        }
    }
}

/// Term-only structural description shared across all continuation sumcheck
/// steps. Per-step source data is passed separately to the compact builder,
/// so the term-only form is enough for `FlatContinuationBuildPlan`.
#[derive(Clone)]
pub(crate) struct FlatContinuationTermDesc {
    pub(crate) num_sources: u32,

    pub(crate) c0_only_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR]>,
    pub(crate) num_c0_only_linear: u32,

    pub(crate) unified_quadratic: Box<[GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC]>,
    pub(crate) num_unified_quadratic: u32,

    pub(crate) unified_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR]>,
    pub(crate) num_unified_linear: u32,

    pub(crate) num_constants: u32,
}

impl Default for FlatContinuationTermDesc {
    fn default() -> Self {
        Self {
            num_sources: 0,
            c0_only_linear: Box::new([GpuFlatC0Ref::default(); FLAT_CONT_MAX_C0_ONLY_LINEAR]),
            num_c0_only_linear: 0,
            unified_quadratic: Box::new(
                [GpuFlatC1Pair::default(); FLAT_CONT_MAX_UNIFIED_QUADRATIC],
            ),
            num_unified_quadratic: 0,
            unified_linear: Box::new([GpuFlatC0Ref::default(); FLAT_CONT_MAX_UNIFIED_LINEAR]),
            num_unified_linear: 0,
            num_constants: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Continuation build plan
// ---------------------------------------------------------------------------

/// Complete build plan for the flat continuation kernel.
/// `term_desc` holds the shared term arrays (same for all steps).
/// Source entries are populated per step from prepared storage.
pub(crate) struct FlatContinuationBuildPlan<E> {
    pub(crate) term_desc: FlatContinuationTermDesc,
    pub(crate) recipes: Vec<CoefficientRecipe<E>>,
    /// One entry per unique source: records the first (gate_idx, is_ext, input_idx)
    /// that mapped to a source table index. Used to populate per-step source entries.
    pub(crate) source_assignments: Vec<ContinuationSourceAssignment>,
}

/// Records which source table slot a particular gate input maps to.
#[derive(Clone)]
pub(crate) struct ContinuationSourceAssignment {
    pub(crate) gate_idx: usize,
    pub(crate) is_ext: bool,
    pub(crate) input_idx: usize,
    pub(crate) source_table_idx: u32,
}

impl<E: Field + field::FieldExtension<BF>> FlatContinuationBuildPlan<E> {
    pub(crate) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }
}
