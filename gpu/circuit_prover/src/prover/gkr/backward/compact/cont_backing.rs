//! Continuation (rounds ≥ 3) reverse-map over the consolidated folding
//! backings plus the compact descriptor builder that consumes a
//! `FlatContinuationBuildPlan` and produces the matching unified compact
//! descriptor.

use super::super::super::GpuGKRStorage;
use super::super::flat::{
    FlatContinuationBuildPlan, GpuFlatContinuingSourceEntry, GpuFlatUnifiedTerm,
    FLAT_CONT_MAX_SOURCES, FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS,
    FLAT_CONT_UNIFIED_MAX_TILES, FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE, TERM_TYPE_C0_ONLY_LINEAR,
    TERM_TYPE_CONSTANT, TERM_TYPE_UNIFIED_LINEAR, TERM_TYPE_UNIFIED_QUADRATIC,
};
use super::super::kernels::{
    pack_cache_u16, pack_source_u16, GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::cont_descs::{FlatTermTablesHost, GpuFlatContinuationUnifiedDesc};
use super::encoding::FLAT_SOURCE_POLY_IDX_MASK;
use crate::primitives::field::BF;
use crate::upstream::Field;

#[derive(Clone, Copy)]
pub(crate) struct ContinuationBackingRange {
    pub(crate) base: *const u8,
    pub(crate) start_byte: usize,
    pub(crate) end_byte: usize,
    pub(crate) elem_bytes: usize,
    /// `log2(per_poly_size_in_elements)`. The consolidated folding backing's
    /// per-poly stride matches the layer layout's `log2_stride`.
    pub(crate) log2_stride: u32,
}

pub(crate) fn build_continuation_backing_ranges<E: Field>(
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
pub(crate) fn resolve_continuation_backing_for_pointer(
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
pub(crate) fn build_flat_continuation_unified_desc<E: Field>(
    sources: &[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES],
    plan: &FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> (Box<GpuFlatContinuationUnifiedDesc>, Option<FlatTermTablesHost>) {
    use std::collections::HashSet;

    let mut compact = Box::new(GpuFlatContinuationUnifiedDesc::default());
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
    // NOTE: `total_terms` may exceed FLAT_CONT_UNIFIED_MAX_TERMS on large
    // delegations → device-terms path (Stage 3b); no assert here.

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
    // NOTE: `num_tiles` may exceed FLAT_CONT_UNIFIED_MAX_TILES on large
    // delegations → device-terms path (Stage 3b); no assert here.

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
