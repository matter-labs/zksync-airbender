//! Stateful builder that emits the flat round-0 source table and term arrays
//! while accumulating per-tier coefficient recipes.

use std::collections::HashMap;

use super::super::super::{
    GpuBaseFieldPolySource, GpuExtensionFieldPolyInitialSource, GpuGKRStorage,
};
use super::super::compact::{
    build_backing_ranges, pack_flat_round0_source_real, pack_flat_round0_source_virtual,
    resolve_backing_for_pointer, BackingRange, FlatRound0BuildPlan, GpuFlatRound0StaticDesc,
};
use super::super::kernels::{GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS};
use super::types::{
    CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair, FLAT_ROUND0_MAX_C0_BF, FLAT_ROUND0_MAX_C0_EXT,
    FLAT_ROUND0_MAX_C1_BF_BF, FLAT_ROUND0_MAX_C1_BF_E4, FLAT_ROUND0_MAX_C1_E4_E4,
    FLAT_ROUND0_MAX_C1_LINEAR, FLAT_ROUND0_MAX_SOURCES,
};
use crate::primitives::field::BF;
use crate::upstream::Field;

pub(crate) struct FlatDescriptionBuilder<'s, E: Field> {
    desc: Box<GpuFlatRound0StaticDesc>,
    // Per-tier recipe Vecs — concatenated in tier order in finish().
    recipes_c0_bf: Vec<CoefficientRecipe<E>>,
    recipes_c0_ext: Vec<CoefficientRecipe<E>>,
    recipes_c1_bf_bf: Vec<CoefficientRecipe<E>>,
    recipes_c1_e4_e4: Vec<CoefficientRecipe<E>>,
    recipes_c1_bf_e4: Vec<CoefficientRecipe<E>>,
    recipes_c1_linear: Vec<CoefficientRecipe<E>>,
    /// Dedup: maps the packed `u16` source representation to the index in
    /// `desc.sources[]` where it was first emitted. Identical references
    /// (same virtual kind, or same `(slot, poly_idx)`) collapse to one entry.
    source_map: HashMap<u16, u32>,
    // Compact-source resolution state:
    /// Per-launch slot table: distinct backing base pointers seen, in
    /// first-appearance order. Mirrored into `desc.tables.bases` /
    /// `desc.tables.log2_stride` as new slots are assigned.
    backing_slot: HashMap<usize, u8>,
    next_slot: u8,
    /// Pre-computed byte ranges of every `(layer, class)` consolidated
    /// backing in `storage`. `add_*_source` looks each raw poly pointer
    /// up here to recover `(base, log2_stride, poly_idx)`.
    ranges: Vec<BackingRange>,
    _storage: std::marker::PhantomData<&'s ()>,
}

impl<'s, E: Field> FlatDescriptionBuilder<'s, E> {
    pub(crate) fn new(storage: &'s GpuGKRStorage<BF, E>) -> Self {
        Self {
            desc: Box::new(GpuFlatRound0StaticDesc::default()),
            recipes_c0_bf: Vec::new(),
            recipes_c0_ext: Vec::new(),
            recipes_c1_bf_bf: Vec::new(),
            recipes_c1_e4_e4: Vec::new(),
            recipes_c1_bf_e4: Vec::new(),
            recipes_c1_linear: Vec::new(),
            source_map: HashMap::new(),
            backing_slot: HashMap::with_capacity(GKR_DIM_REDUCING_BASE_SLOTS),
            next_slot: 0,
            ranges: build_backing_ranges(storage),
            _storage: std::marker::PhantomData,
        }
    }

    /// Resolve `(base, log2_stride)` to a slot in `desc.tables`, allocating a
    /// new slot on first appearance. Panics if the static slot count is
    /// exceeded.
    fn assign_slot(&mut self, base: *const u8, log2_stride: u32) -> u8 {
        let key = base as usize;
        if let Some(&s) = self.backing_slot.get(&key) {
            return s;
        }
        let s = self.next_slot;
        assert!(
            (s as usize) < GKR_DIM_REDUCING_BASE_SLOTS,
            "flat round0: distinct backing count exceeds {GKR_DIM_REDUCING_BASE_SLOTS}",
        );
        self.backing_slot.insert(key, s);
        self.desc.tables.bases[s as usize] = base;
        self.desc.tables.log2_stride[s as usize] = log2_stride;
        self.next_slot += 1;
        s
    }

    /// Insert a packed source into the source table, deduping against
    /// previous entries that produce the same `u16`.
    fn intern_source(&mut self, packed: u16) -> u32 {
        if let Some(&idx) = self.source_map.get(&packed) {
            return idx;
        }
        let idx = self.desc.num_sources;
        assert!(
            (idx as usize) < FLAT_ROUND0_MAX_SOURCES,
            "flat round0: source table overflow ({idx} >= {FLAT_ROUND0_MAX_SOURCES})",
        );
        self.desc.sources[idx as usize] = GpuGKRSourceRecord::source_only(packed);
        self.desc.num_sources = idx + 1;
        self.source_map.insert(packed, idx);
        idx
    }

    pub(crate) fn add_bf_source<B>(&mut self, src: &GpuBaseFieldPolySource<B>) -> u32 {
        let packed = if src.source_kind as u32 >= 2 {
            // Virtual base-field source (range-check, inits/teardowns): the
            // kind discriminant fully identifies it; round 0 has no
            // folding-cache mate, so bit 15 doubles as the virtual flag.
            pack_flat_round0_source_virtual(src.source_kind as u8)
        } else {
            // Real consolidated poly. Resolve the raw start pointer back to
            // its `(base, log2_stride, poly_idx)` via the storage range map.
            let raw = src.start as *const u8;
            let (base, log2_stride, poly_idx) = resolve_backing_for_pointer(&self.ranges, raw)
                .unwrap_or_else(|| {
                    panic!(
                        "flat round0: source pointer {raw:?} does not fall \
                         within any consolidated storage backing",
                    )
                });
            let slot = self.assign_slot(base, log2_stride);
            pack_flat_round0_source_real(slot, poly_idx)
        };
        self.intern_source(packed)
    }

    pub(crate) fn add_ext_source(&mut self, src: &GpuExtensionFieldPolyInitialSource<E>) -> u32 {
        let raw = src.start as *const u8;
        let (base, log2_stride, poly_idx) = resolve_backing_for_pointer(&self.ranges, raw)
            .unwrap_or_else(|| {
                panic!(
                    "flat round0: ext source pointer {raw:?} does not fall \
                     within any consolidated storage backing",
                )
            });
        let slot = self.assign_slot(base, log2_stride);
        let packed = pack_flat_round0_source_real(slot, poly_idx);
        self.intern_source(packed)
    }

    // --- Term pushers ---

    pub(crate) fn push_c0_bf(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_c0_bf as usize;
        assert!(i < FLAT_ROUND0_MAX_C0_BF, "flat round0: c0_bf overflow");
        self.desc.c0_bf[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c0_bf += 1;
        self.recipes_c0_bf.push(recipe);
    }

    pub(crate) fn push_c0_ext(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_c0_ext as usize;
        assert!(i < FLAT_ROUND0_MAX_C0_EXT, "flat round0: c0_ext overflow");
        self.desc.c0_ext[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c0_ext += 1;
        self.recipes_c0_ext.push(recipe);
    }

    pub(crate) fn push_c1_bf_bf(
        &mut self,
        source_a: u32,
        source_b: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_c1_bf_bf as usize;
        assert!(
            i < FLAT_ROUND0_MAX_C1_BF_BF,
            "flat round0: c1_bf_bf overflow"
        );
        self.desc.c1_bf_bf[i] = GpuFlatC1Pair {
            source_a: source_a as u16,
            source_b: source_b as u16,
        };
        self.desc.num_c1_bf_bf += 1;
        self.recipes_c1_bf_bf.push(recipe);
    }

    pub(crate) fn push_c1_e4_e4(
        &mut self,
        source_a: u32,
        source_b: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_c1_e4_e4 as usize;
        assert!(
            i < FLAT_ROUND0_MAX_C1_E4_E4,
            "flat round0: c1_e4_e4 overflow"
        );
        self.desc.c1_e4_e4[i] = GpuFlatC1Pair {
            source_a: source_a as u16,
            source_b: source_b as u16,
        };
        self.desc.num_c1_e4_e4 += 1;
        self.recipes_c1_e4_e4.push(recipe);
    }

    pub(crate) fn push_c1_bf_e4(
        &mut self,
        source_bf: u32,
        source_e4: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_c1_bf_e4 as usize;
        assert!(
            i < FLAT_ROUND0_MAX_C1_BF_E4,
            "flat round0: c1_bf_e4 overflow"
        );
        self.desc.c1_bf_e4[i] = GpuFlatC1Pair {
            source_a: source_bf as u16,
            source_b: source_e4 as u16,
        };
        self.desc.num_c1_bf_e4 += 1;
        self.recipes_c1_bf_e4.push(recipe);
    }

    pub(crate) fn push_c1_linear(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_c1_linear as usize;
        assert!(
            i < FLAT_ROUND0_MAX_C1_LINEAR,
            "flat round0: c1_linear overflow"
        );
        self.desc.c1_linear[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c1_linear += 1;
        self.recipes_c1_linear.push(recipe);
    }

    pub(crate) fn finish(self) -> FlatRound0BuildPlan<E> {
        // Concatenate recipes in tier order to match kernel's *coeff++ traversal.
        let mut recipes = self.recipes_c0_bf;
        recipes.extend(self.recipes_c0_ext);
        recipes.extend(self.recipes_c1_bf_bf);
        recipes.extend(self.recipes_c1_e4_e4);
        recipes.extend(self.recipes_c1_bf_e4);
        recipes.extend(self.recipes_c1_linear);
        FlatRound0BuildPlan {
            static_desc: self.desc,
            recipes,
        }
    }
}
