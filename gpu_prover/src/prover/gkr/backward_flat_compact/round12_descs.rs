use field::Field;

use super::super::backward_flat::{
    GpuFlatUnifiedTerm, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
    FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES, FLAT_CONT_UNIFIED_MAX_TERMS, FLAT_CONT_UNIFIED_MAX_TILES,
};
use super::super::backward_kernels::{
    pack_cache_u16, pack_source_u16, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::super::{GpuBaseFieldSourceKind, GpuGKRStorage};
use super::{
    build_backing_ranges, build_continuation_backing_ranges, resolve_backing_for_pointer,
    resolve_continuation_backing_for_pointer, BackingRange, ContinuationBackingRange,
    GpuFlatRound1UnifiedDescCompact, GpuFlatRound2UnifiedDescCompact, CONT_BASE_CACHE_VIRTUAL_FLAG,
    CONT_BASE_FIRST_ACCESS_FLAG, CONT_BASE_VIRTUAL_KIND_MASK,
};
use crate::primitives::field::BF;

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
pub(in crate::prover::gkr) fn build_flat_round1_unified_desc_compact<E: Field>(
    round1_fused: &super::super::backward_flat::Round1FusedSources,
    plan: &super::super::backward_flat::FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Box<GpuFlatRound1UnifiedDescCompact> {
    use super::super::backward_flat::{
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

/// Resolve a round-2 cache pointer. For base sources at round 2,
/// `this_layer_cache_start = buffer.initial_pointer()` (sub_offset=0), same
/// as round 1. For ext sources at round 2 (sumcheck_step=2),
/// `pointer_for_sumcheck_continuation(2)` returns `(buffer_start, buffer_start
/// + size_after_one_fold)` — both within the consolidated ext-folding Arc.
/// `previous_layer_start` is at sub_offset=0; `this_layer_cache_start` is at
/// sub_offset=`size_after_one_fold`. sub_offset is not validated here
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
pub(in crate::prover::gkr) fn build_flat_round2_unified_desc_compact<E: Field>(
    round2_fused: &super::super::backward_flat::Round2FusedSources,
    plan: &super::super::backward_flat::FlatContinuationBuildPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
) -> Box<GpuFlatRound2UnifiedDescCompact> {
    use super::super::backward_flat::{
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
