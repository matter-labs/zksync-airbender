//! Compact continuation descriptor construction and round-local arena binding.

use super::super::flat::{
    FlatContinuationBuildPlan, GpuFlatUnifiedTerm, FLAT_CONT_MAX_SOURCES,
    FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES,
    FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE, TERM_TYPE_C0_ONLY_LINEAR, TERM_TYPE_CONSTANT,
    TERM_TYPE_UNIFIED_LINEAR, TERM_TYPE_UNIFIED_QUADRATIC,
};
use super::super::kernels::{
    pack_cache_u16, pack_source_u16, GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::cont_descs::{FlatTermTablesHost, GpuFlatContinuationUnifiedDesc};
use super::encoding::{FoldingArenaBinding, FLAT_SOURCE_POLY_IDX_MASK};

pub(in crate::backward) fn rebind_flat_continuation_descriptor<E>(
    desc: &mut GpuFlatContinuationUnifiedDesc,
    current: FoldingArenaBinding,
    destination: FoldingArenaBinding,
) {
    let num_sources = desc.num_sources as usize;
    let sources_per_slot = FLAT_SOURCE_POLY_IDX_MASK as usize + 1;
    let chunks = num_sources.div_ceil(sources_per_slot);
    assert!(2 * chunks <= GKR_DIM_REDUCING_BASE_SLOTS);
    desc.tables = Default::default();
    for chunk in 0..chunks {
        let current_elements = (chunk * sources_per_slot) << current.log2_stride;
        desc.tables.bases[chunk] = current
            .base
            .wrapping_add(current_elements * std::mem::size_of::<E>());
        desc.tables.log2_stride[chunk] = current.log2_stride;
        let destination_slot = chunks + chunk;
        let destination_elements = (chunk * sources_per_slot) << destination.log2_stride;
        desc.tables.bases[destination_slot] = destination
            .base
            .wrapping_add(destination_elements * std::mem::size_of::<E>());
        desc.tables.log2_stride[destination_slot] = destination.log2_stride;
    }
    desc.prev_per_poly_offset = [0; GKR_DIM_REDUCING_BASE_SLOTS];
    desc.cache_per_poly_offset = [0; GKR_DIM_REDUCING_BASE_SLOTS];
    for (idx, record) in desc.sources[..num_sources].iter_mut().enumerate() {
        let slot = idx / sources_per_slot;
        let poly_idx = (idx % sources_per_slot) as u16;
        *record = GpuGKRSourceRecord::new(
            pack_source_u16(true, slot as u8, poly_idx),
            pack_cache_u16((chunks + slot) as u8, poly_idx),
        );
    }
}

// ---------------------------------------------------------------------------
// Builder: structural plan → compact unified descriptor
// ---------------------------------------------------------------------------
pub(crate) fn build_flat_continuation_unified_desc(
    plan: &FlatContinuationBuildPlan,
) -> (
    Box<GpuFlatContinuationUnifiedDesc>,
    Option<FlatTermTablesHost>,
) {
    use std::collections::HashSet;

    let mut compact = Box::new(GpuFlatContinuationUnifiedDesc::default());
    let term_desc = &plan.term_desc;

    // ----- Source encoding pass -----
    let n = term_desc.num_sources as usize;
    assert!(
        n <= FLAT_CONT_MAX_SOURCES,
        "compact continuation: num_sources {n} exceeds FLAT_CONT_MAX_SOURCES {FLAT_CONT_MAX_SOURCES}",
    );
    compact.num_sources = term_desc.num_sources;
    let sources_per_slot = FLAT_SOURCE_POLY_IDX_MASK as usize + 1;
    let chunks = n.div_ceil(sources_per_slot);
    assert!(2 * chunks <= GKR_DIM_REDUCING_BASE_SLOTS);
    for (i, record) in compact.sources[..n].iter_mut().enumerate() {
        let slot = i / sources_per_slot;
        let poly_idx = (i % sources_per_slot) as u16;
        *record = GpuGKRSourceRecord::new(
            pack_source_u16(true, slot as u8, poly_idx),
            pack_cache_u16((chunks + slot) as u8, poly_idx),
        );
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
    // NOTE: `total_terms` may exceed FLAT_CONT_UNIFIED_MAX_TERMS on large
    // delegations → device-terms path; no assert here.

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
        for (i, term) in terms.iter().enumerate().skip(num_constant_terms + 1) {
            let key = tile_key(term);
            if key != current_key {
                tile_boundaries.push((tile_start, i));
                current_key = key;
                tile_start = i;
            }
        }
        tile_boundaries.push((tile_start, terms.len()));
    }

    let num_tiles = tile_boundaries.len();
    // NOTE: `num_tiles` may exceed FLAT_CONT_UNIFIED_MAX_TILES on large
    // delegations → device-terms path; no assert here.

    let mut fold_sources: Vec<u16> = Vec::new();
    let mut tile_term_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut tile_fold_offsets: Vec<u16> = Vec::with_capacity(num_tiles + 1);
    let mut folded: HashSet<u16> = HashSet::new();

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
            if folded.insert(src) {
                fold_sources.push(src);
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

    compact.num_terms = terms.len() as u32;
    compact.num_constant_terms = num_constant_terms as u32;
    compact.num_tiles = num_tiles as u32;
    compact.fold_sources[..fold_sources.len()].copy_from_slice(&fold_sources);

    if terms.len() <= FLAT_CONT_UNIFIED_MAX_TERMS && num_tiles <= FLAT_CONT_UNIFIED_MAX_TILES {
        compact.terms[..terms.len()].copy_from_slice(&terms);
        compact.tile_term_offsets[..tile_term_offsets.len()].copy_from_slice(&tile_term_offsets);
        compact.tile_fold_offsets[..tile_fold_offsets.len()].copy_from_slice(&tile_fold_offsets);
        (compact, None)
    } else {
        (
            compact,
            Some(FlatTermTablesHost {
                terms,
                tile_term_offsets,
                tile_fold_offsets,
            }),
        )
    }
}
