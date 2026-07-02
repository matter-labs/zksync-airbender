use std::collections::HashMap;

use super::super::{CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair};
use super::types::{
    ContinuationSourceAssignment, FlatContinuationBuildPlan, FlatContinuationTermDesc,
    FLAT_CONT_MAX_C0_ONLY_LINEAR, FLAT_CONT_MAX_CONSTANT, FLAT_CONT_MAX_SOURCES,
    FLAT_CONT_MAX_UNIFIED_LINEAR, FLAT_CONT_MAX_UNIFIED_QUADRATIC,
};
use crate::upstream::Field;

/// Apply an index permutation in-place to a slice.
fn apply_permutation<T: Copy + Default>(order: &[usize], data: &mut [T]) {
    let tmp: Vec<T> = order.iter().map(|&i| data[i]).collect();
    data[..order.len()].copy_from_slice(&tmp);
}

/// Apply an index permutation in-place to a Vec.
fn apply_permutation_vec<T: Clone>(order: &[usize], data: &mut Vec<T>) {
    let tmp: Vec<T> = order.iter().map(|&i| data[i].clone()).collect();
    *data = tmp;
}

/// Key for deduplicating continuation sources.
/// We deduplicate by cache pointer plus source kind (base/ext), since round 1/2
/// require base/ext separation even when the underlying continuation cache is shared.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ContinuationSourceKey {
    cache_ptr: usize,
    is_ext: bool,
}

pub(in crate::prover::gkr::backward::flat) struct FlatContinuationDescriptionBuilder<E> {
    desc: FlatContinuationTermDesc,
    num_sources: u32,
    recipes_constants: Vec<CoefficientRecipe<E>>,
    recipes_c0_only: Vec<CoefficientRecipe<E>>,
    recipes_quadratic: Vec<CoefficientRecipe<E>>,
    recipes_linear: Vec<CoefficientRecipe<E>>,
    source_map: HashMap<ContinuationSourceKey, u32>,
    source_assignments: Vec<ContinuationSourceAssignment>,
}

impl<E: Field> FlatContinuationDescriptionBuilder<E> {
    pub(in crate::prover::gkr::backward::flat) fn new() -> Self {
        Self {
            desc: FlatContinuationTermDesc::default(),
            num_sources: 0,
            recipes_constants: Vec::new(),
            recipes_c0_only: Vec::new(),
            recipes_quadratic: Vec::new(),
            recipes_linear: Vec::new(),
            source_map: HashMap::new(),
            source_assignments: Vec::new(),
        }
    }

    /// Register a source by its cache pointer and return its index.
    /// The actual source entry (prev, cache) is populated per step later.
    pub(in crate::prover::gkr::backward::flat) fn add_source(
        &mut self,
        cache_ptr: usize,
        gate_idx: usize,
        is_ext: bool,
        input_idx: usize,
    ) -> u32 {
        let key = ContinuationSourceKey { cache_ptr, is_ext };
        if let Some(&idx) = self.source_map.get(&key) {
            return idx;
        }
        let idx = self.num_sources;
        assert!(
            (idx as usize) < FLAT_CONT_MAX_SOURCES,
            "flat continuation: source table overflow ({idx} >= {FLAT_CONT_MAX_SOURCES})",
        );
        self.num_sources = idx + 1;
        self.source_map.insert(key, idx);
        self.source_assignments.push(ContinuationSourceAssignment {
            gate_idx,
            is_ext,
            input_idx,
            source_table_idx: idx,
        });
        idx
    }

    pub(in crate::prover::gkr::backward::flat) fn push_constant(
        &mut self,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_constants as usize;
        assert!(
            i < FLAT_CONT_MAX_CONSTANT,
            "flat continuation: constant overflow"
        );
        self.desc.num_constants += 1;
        self.recipes_constants.push(recipe);
    }

    pub(in crate::prover::gkr::backward::flat) fn push_c0_only_linear(
        &mut self,
        source_idx: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_c0_only_linear as usize;
        assert!(
            i < FLAT_CONT_MAX_C0_ONLY_LINEAR,
            "flat continuation: c0_only_linear overflow"
        );
        self.desc.c0_only_linear[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c0_only_linear += 1;
        self.recipes_c0_only.push(recipe);
    }

    pub(in crate::prover::gkr::backward::flat) fn push_unified_quadratic(
        &mut self,
        source_a: u32,
        source_b: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_unified_quadratic as usize;
        assert!(
            i < FLAT_CONT_MAX_UNIFIED_QUADRATIC,
            "flat continuation: unified_quadratic overflow"
        );
        self.desc.unified_quadratic[i] = GpuFlatC1Pair {
            source_a: source_a as u16,
            source_b: source_b as u16,
        };
        self.desc.num_unified_quadratic += 1;
        self.recipes_quadratic.push(recipe);
    }

    // No gate emits a continuation `unified_linear` term: the materialize gate
    // (its only former caller) now uses `push_c0_only_linear`, matching the CPU
    // `evaluate_linear_term` which contributes to c0 only at rounds >= 1. The
    // tier + its device descriptor are retained (kept in Rust↔CUDA lockstep) for
    // potential future gates and to avoid a descriptor-layout churn.
    #[allow(dead_code)]
    pub(in crate::prover::gkr::backward::flat) fn push_unified_linear(
        &mut self,
        source_idx: u32,
        recipe: CoefficientRecipe<E>,
    ) {
        let i = self.desc.num_unified_linear as usize;
        assert!(
            i < FLAT_CONT_MAX_UNIFIED_LINEAR,
            "flat continuation: unified_linear overflow"
        );
        self.desc.unified_linear[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_unified_linear += 1;
        self.recipes_linear.push(recipe);
    }

    pub(in crate::prover::gkr::backward::flat) fn finish(mut self) -> FlatContinuationBuildPlan<E> {
        // Sort terms within each category by source-group affinity so that
        // terms accessing the same sources are adjacent, improving L1 reuse.
        self.sort_terms_by_source_group();

        // Concatenate recipes in tier order to match kernel's *coeff++ traversal:
        // constants, c0_only_linear, unified_quadratic, unified_linear
        let mut recipes = self.recipes_constants;
        recipes.extend(self.recipes_c0_only);
        recipes.extend(self.recipes_quadratic);
        recipes.extend(self.recipes_linear);
        let mut term_desc = self.desc;
        term_desc.num_sources = self.num_sources;
        FlatContinuationBuildPlan {
            term_desc,
            recipes,
            source_assignments: self.source_assignments,
        }
    }

    /// Reorder terms within each category so that terms accessing the same
    /// source groups are clustered together.  This improves L1 cache reuse
    /// in the GPU kernel without any kernel-side changes.
    fn sort_terms_by_source_group(&mut self) {
        const SOURCE_GROUP_SIZE: u16 = 2;

        let group = |idx: u16| idx / SOURCE_GROUP_SIZE;

        // --- unified_quadratic: sort by (min_group, max_group, source_a, source_b) ---
        {
            let n = self.desc.num_unified_quadratic as usize;
            let mut order: Vec<usize> = (0..n).collect();
            let terms = &self.desc.unified_quadratic[..n];
            order.sort_by(|&a, &b| {
                let ta = terms[a];
                let tb = terms[b];
                let (ga_lo, ga_hi) = {
                    let g0 = group(ta.source_a);
                    let g1 = group(ta.source_b);
                    (g0.min(g1), g0.max(g1))
                };
                let (gb_lo, gb_hi) = {
                    let g0 = group(tb.source_a);
                    let g1 = group(tb.source_b);
                    (g0.min(g1), g0.max(g1))
                };
                (ga_lo, ga_hi, ta.source_a, ta.source_b).cmp(&(
                    gb_lo,
                    gb_hi,
                    tb.source_a,
                    tb.source_b,
                ))
            });
            apply_permutation(&order, &mut self.desc.unified_quadratic[..n]);
            apply_permutation_vec(&order, &mut self.recipes_quadratic);
        }

        // --- c0_only_linear: sort by source group ---
        {
            let n = self.desc.num_c0_only_linear as usize;
            let mut order: Vec<usize> = (0..n).collect();
            let terms = &self.desc.c0_only_linear[..n];
            order.sort_by(|&a, &b| {
                let sa = group(terms[a].source_idx);
                let sb = group(terms[b].source_idx);
                sa.cmp(&sb)
                    .then(terms[a].source_idx.cmp(&terms[b].source_idx))
            });
            apply_permutation(&order, &mut self.desc.c0_only_linear[..n]);
            apply_permutation_vec(&order, &mut self.recipes_c0_only);
        }

        // --- unified_linear: sort by source group ---
        {
            let n = self.desc.num_unified_linear as usize;
            let mut order: Vec<usize> = (0..n).collect();
            let terms = &self.desc.unified_linear[..n];
            order.sort_by(|&a, &b| {
                let sa = group(terms[a].source_idx);
                let sb = group(terms[b].source_idx);
                sa.cmp(&sb)
                    .then(terms[a].source_idx.cmp(&terms[b].source_idx))
            });
            apply_permutation(&order, &mut self.desc.unified_linear[..n]);
            apply_permutation_vec(&order, &mut self.recipes_linear);
        }
    }
}
