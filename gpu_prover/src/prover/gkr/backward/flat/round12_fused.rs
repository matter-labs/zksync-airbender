//! Round 1 / Round 2 fused-source descriptors. Each round mixes a per-round
//! base-field source entry (`gkr_base_after_one_source` /
//! `gkr_base_after_two_source`) with the shared continuing ext source entry,
//! plus an `idx_remap` that maps the continuation plan's flat source-table
//! index to the round's tagged base/ext index.

use super::super::super::GpuBaseFieldSourceKind;
use super::continuation::{
    GpuFlatContinuingSourceEntry, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
};

// ===========================================================================
// Round 1 static description (mixed base_after_one + continuing sources)
// ===========================================================================

/// Base-after-one source entry — mirrors `gkr_base_after_one_source<bf, e4>` layout.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatBaseAfterOneSourceEntry {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const u8,     // *const bf
    pub(crate) this_layer_cache_start: *mut u8, // *mut E4
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

unsafe impl Send for GpuFlatBaseAfterOneSourceEntry {}
unsafe impl Sync for GpuFlatBaseAfterOneSourceEntry {}

impl Default for GpuFlatBaseAfterOneSourceEntry {
    fn default() -> Self {
        Self {
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_input_start: std::ptr::null(),
            this_layer_cache_start: std::ptr::null_mut(),
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

/// Round 1 fused-source data: split base/ext arrays produced from the
/// continuation plan's source assignments, plus an `idx_remap` that maps
/// the plan's flat source-table index to the round-1 tagged index
/// (`FLAT_CONT_EXT_SOURCE_BIT` set for ext entries).
///
/// Term arrays live in `plan.term_desc` and the compact builder applies
/// `idx_remap` inline as it constructs compact term records.
pub(crate) struct Round1FusedSources {
    pub(crate) base_sources: Box<[GpuFlatBaseAfterOneSourceEntry; FLAT_CONT_MAX_BASE_SOURCES]>,
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES]>,
    pub(crate) num_ext_sources: u32,
    pub(crate) idx_remap: Vec<u16>,
}

unsafe impl Send for Round1FusedSources {}
unsafe impl Sync for Round1FusedSources {}

impl Default for Round1FusedSources {
    fn default() -> Self {
        Self {
            base_sources: Box::new(
                [GpuFlatBaseAfterOneSourceEntry::default(); FLAT_CONT_MAX_BASE_SOURCES],
            ),
            num_base_sources: 0,
            ext_sources: Box::new(
                [GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_EXT_SOURCES],
            ),
            num_ext_sources: 0,
            idx_remap: Vec::new(),
        }
    }
}

// ===========================================================================
// Round 2 static description (mixed base_after_two + continuing sources)
// ===========================================================================

/// Base-after-two source entry — mirrors `gkr_base_after_two_source<bf, e4>` layout.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuFlatBaseAfterTwoSourceEntry {
    pub(crate) base_input_start: *const u8,     // *const bf
    pub(crate) this_layer_cache_start: *mut u8, // *mut E4
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

unsafe impl Send for GpuFlatBaseAfterTwoSourceEntry {}
unsafe impl Sync for GpuFlatBaseAfterTwoSourceEntry {}

impl Default for GpuFlatBaseAfterTwoSourceEntry {
    fn default() -> Self {
        Self {
            base_input_start: std::ptr::null(),
            this_layer_cache_start: std::ptr::null_mut(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

/// Round 2 fused-source data: split base/ext arrays produced from the
/// continuation plan's source assignments, plus an `idx_remap` that maps
/// the plan's flat source-table index to the round-2 tagged index
/// (`FLAT_CONT_EXT_SOURCE_BIT` set for ext entries). Mirrors
/// `Round1FusedSources` with the round-2 base-source entry shape.
pub(crate) struct Round2FusedSources {
    pub(crate) base_sources: Box<[GpuFlatBaseAfterTwoSourceEntry; FLAT_CONT_MAX_BASE_SOURCES]>,
    pub(crate) num_base_sources: u32,
    pub(crate) ext_sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES]>,
    pub(crate) num_ext_sources: u32,
    pub(crate) idx_remap: Vec<u16>,
}

unsafe impl Send for Round2FusedSources {}
unsafe impl Sync for Round2FusedSources {}

impl Default for Round2FusedSources {
    fn default() -> Self {
        Self {
            base_sources: Box::new(
                [GpuFlatBaseAfterTwoSourceEntry::default(); FLAT_CONT_MAX_BASE_SOURCES],
            ),
            num_base_sources: 0,
            ext_sources: Box::new(
                [GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_EXT_SOURCES],
            ),
            num_ext_sources: 0,
            idx_remap: Vec::new(),
        }
    }
}
