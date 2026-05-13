use std::collections::HashMap;
use std::ffi::c_void;

use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;
use field::{Field, PrimeField};

use super::super::backward_kernels::{
    GpuGKRMainLayerConstraintChallengeTerm, GpuGKRMainLayerConstraintMetadataSource,
    GpuGKRMainLayerDeferredChallengeSource, GpuGKRMainLayerKernelKind,
};
use super::super::GpuExtensionFieldPolyContinuingSourcePlan;
use super::{
    immediate_recipe_with_negation, CoefficientRecipe, GpuFlatC0Ref, GpuFlatC1Pair,
    NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::eval_recipes::GpuFlatRecipeEvalDesc;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;

pub(in crate::prover::gkr) const FLAT_CONT_CONST_MAX: usize = 1024;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_SOURCES: usize = 512;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_C0_ONLY_LINEAR: usize = 640;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_UNIFIED_QUADRATIC: usize = 4608;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_UNIFIED_LINEAR: usize = 128;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_CONSTANT: usize = 64;

// Round 1/2 mixed source limits
pub(in crate::prover::gkr) const FLAT_CONT_MAX_BASE_SOURCES: usize = 128;
pub(in crate::prover::gkr) const FLAT_CONT_MAX_EXT_SOURCES: usize = 384;
pub(in crate::prover::gkr) const FLAT_CONT_EXT_SOURCE_BIT: u16 = 0x8000;

// Unified tiled kernel constants
pub(in crate::prover::gkr) const FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE: usize = 4;
#[allow(dead_code)]
pub(in crate::prover::gkr) const FLAT_CONT_UNIFIED_MAX_GRID_DIM: usize =
    (FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES) / FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE;
pub(in crate::prover::gkr) const FLAT_CONT_UNIFIED_MAX_TERMS: usize = 1024;
// Sparse: only non-empty tiles stored. Each tile has ≥1 term, so max tiles ≤ max terms.
pub(in crate::prover::gkr) const FLAT_CONT_UNIFIED_MAX_TILES: usize = FLAT_CONT_UNIFIED_MAX_TERMS;
pub(in crate::prover::gkr) const FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES: usize =
    FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES;

// ---------------------------------------------------------------------------
// Static description types (mirror CUDA structs)
// ---------------------------------------------------------------------------

/// Compact source descriptor for continuing sources.
/// `previous_layer_start == null` encodes `!first_access` (read from cache).
#[repr(C)]
#[derive(Clone, Copy)]
pub(in crate::prover::gkr) struct GpuFlatContinuingSourceEntry {
    pub(in crate::prover::gkr) previous_layer_start: *const u8,
    pub(in crate::prover::gkr) this_layer_cache_start: *mut u8,
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
pub(in crate::prover::gkr) struct FlatContinuationTermDesc {
    pub(in crate::prover::gkr) num_sources: u32,

    pub(in crate::prover::gkr) c0_only_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR]>,
    pub(in crate::prover::gkr) num_c0_only_linear: u32,

    pub(in crate::prover::gkr) unified_quadratic:
        Box<[GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC]>,
    pub(in crate::prover::gkr) num_unified_quadratic: u32,

    pub(in crate::prover::gkr) unified_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR]>,
    pub(in crate::prover::gkr) num_unified_linear: u32,

    pub(in crate::prover::gkr) num_constants: u32,
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
pub(in crate::prover::gkr) struct FlatContinuationBuildPlan<E> {
    pub(in crate::prover::gkr) term_desc: FlatContinuationTermDesc,
    pub(in crate::prover::gkr) recipes: Vec<CoefficientRecipe<E>>,
    /// One entry per unique source: records the first (gate_idx, is_ext, input_idx)
    /// that mapped to a source table index. Used to populate per-step source entries.
    pub(in crate::prover::gkr) source_assignments: Vec<ContinuationSourceAssignment>,
}

/// Records which source table slot a particular gate input maps to.
#[derive(Clone)]
pub(in crate::prover::gkr) struct ContinuationSourceAssignment {
    pub(in crate::prover::gkr) gate_idx: usize,
    pub(in crate::prover::gkr) is_ext: bool,
    pub(in crate::prover::gkr) input_idx: usize,
    pub(in crate::prover::gkr) source_table_idx: u32,
}

impl<E: Field + field::FieldExtension<BF>> FlatContinuationBuildPlan<E> {
    pub(in crate::prover::gkr) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }
}

// ---------------------------------------------------------------------------
// Continuation description builder
// ---------------------------------------------------------------------------

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

pub(in crate::prover::gkr) struct FlatContinuationDescriptionBuilder<E> {
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
    pub(in crate::prover::gkr) fn new() -> Self {
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
    pub(in crate::prover::gkr) fn add_source(
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

    pub(in crate::prover::gkr) fn push_constant(&mut self, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_constants as usize;
        assert!(
            i < FLAT_CONT_MAX_CONSTANT,
            "flat continuation: constant overflow"
        );
        self.desc.num_constants += 1;
        self.recipes_constants.push(recipe);
    }

    pub(in crate::prover::gkr) fn push_c0_only_linear(
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

    pub(in crate::prover::gkr) fn push_unified_quadratic(
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

    pub(in crate::prover::gkr) fn push_unified_linear(
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

    pub(in crate::prover::gkr) fn finish(mut self) -> FlatContinuationBuildPlan<E> {
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

// ---------------------------------------------------------------------------
// Gate decomposition for continuation rounds
// ---------------------------------------------------------------------------

/// Per-gate data needed for building the flat continuation plan.
pub(in crate::prover::gkr) struct PreparedGateForFlatContinuationPlan<'a, E> {
    pub(in crate::prover::gkr) kind: GpuGKRMainLayerKernelKind,
    pub(in crate::prover::gkr) gate_idx: usize,
    /// Base field inputs (as continuing sources in round 3+).
    pub(in crate::prover::gkr) base_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    /// Extension field inputs (as continuing sources).
    pub(in crate::prover::gkr) ext_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    pub(in crate::prover::gkr) batch_challenge_power_offset: u32,
    pub(in crate::prover::gkr) constraint_source:
        Option<&'a GpuGKRMainLayerConstraintMetadataSource<E>>,
}

/// Build the flat continuation plan from prepared gates.
pub(in crate::prover::gkr) fn build_flat_continuation_plan<E: Field>(
    gates: &[PreparedGateForFlatContinuationPlan<'_, E>],
) -> FlatContinuationBuildPlan<E> {
    let mut b = FlatContinuationDescriptionBuilder::<E>::new();

    for gate in gates {
        let p0 = gate.batch_challenge_power_offset;
        let p1 = p0 + 1;

        let bc0 = || -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: false,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![],
            }
        };
        let bc1 = || -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p1,
                negate: false,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![],
            }
        };
        let neg_bc0 = || -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: true,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![],
            }
        };
        let gamma_term = |coeff: BF, power: u32| -> Vec<GpuGKRMainLayerConstraintChallengeTerm> {
            vec![GpuGKRMainLayerConstraintChallengeTerm {
                coeff,
                source: GpuGKRMainLayerDeferredChallengeSource::LookupAdditive,
                power,
            }]
        };
        let bc0_gamma = |coeff: BF, power: u32| -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: false,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![gamma_term(coeff, power)],
            }
        };
        let bc1_gamma = |coeff: BF, power: u32| -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p1,
                negate: false,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![gamma_term(coeff, power)],
            }
        };
        let neg_bc0_gamma = |coeff: BF, power: u32| -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: true,
                immediate_factor: E::ONE,
                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                prefactors: vec![gamma_term(coeff, power)],
            }
        };

        // Helper to add a base input source.
        let add_base = |b: &mut FlatContinuationDescriptionBuilder<E>, idx: usize| -> u32 {
            let src = &gate.base_inputs[idx];
            b.add_source(src.this_layer_start as usize, gate.gate_idx, false, idx)
        };

        // Helper to add an ext input source.
        let add_ext = |b: &mut FlatContinuationDescriptionBuilder<E>, idx: usize| -> u32 {
            let src = &gate.ext_inputs[idx];
            b.add_source(src.this_layer_start as usize, gate.gate_idx, true, idx)
        };

        match gate.kind {
            // ---------------------------------------------------------------
            // Copy gates: c0 = β₀ * f0; c1 = β₀ * f1 [explicit only]
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::BaseCopy => {
                let src = add_base(&mut b, 0);
                b.push_c0_only_linear(src, bc0());
            }

            // ---------------------------------------------------------------
            // LinearBaseOutput: linear constraint evaluation (no quadratic terms)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LinearBaseOutput => {
                emit_continuation_constraint_gate(&mut b, gate, p0);
            }

            GpuGKRMainLayerKernelKind::ExtCopy => {
                let src = add_ext(&mut b, 0);
                b.push_c0_only_linear(src, bc0());
            }

            // ---------------------------------------------------------------
            // Product: c0 = β₀ * f0a * f0b; c1 = β₀ * f1a * f1b
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::Product => {
                let a = add_ext(&mut b, 0);
                let bi = add_ext(&mut b, 1);
                b.push_unified_quadratic(a, bi, bc0());
            }

            // ---------------------------------------------------------------
            // MaskIdentity: c0 = β₀ * mask * value; c1 = β₀ * ...
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::MaskIdentity => {
                let mask = add_base(&mut b, 0);
                let val = add_ext(&mut b, 0);
                // eval0 = mask*value - mask + 1
                // eval1 (compact) uses only the quadratic term.
                b.push_unified_quadratic(mask, val, bc0());
                b.push_c0_only_linear(mask, neg_bc0());
                b.push_constant(bc0());
            }

            // ---------------------------------------------------------------
            // LookupPair: 3 quadratic terms (a×d, c×b, b×d)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupPair => {
                let a = add_ext(&mut b, 0);
                let bi = add_ext(&mut b, 1);
                let c = add_ext(&mut b, 2);
                let d = add_ext(&mut b, 3);
                b.push_unified_quadratic(a, d, bc0());
                b.push_unified_quadratic(c, bi, bc0());
                b.push_unified_quadratic(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // LookupBasePair: 1 quadratic term (b×d)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupBasePair => {
                let bi = add_base(&mut b, 0);
                let d = add_base(&mut b, 1);
                b.push_unified_quadratic(bi, d, bc1());
                b.push_c0_only_linear(bi, bc0());
                b.push_c0_only_linear(d, bc0());
                b.push_constant(bc0_gamma(BF::new(2), 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
                b.push_c0_only_linear(d, bc1_gamma(BF::ONE, 1));
                b.push_constant(bc1_gamma(BF::ONE, 2));
            }

            // ---------------------------------------------------------------
            // LookupBaseMinusMultiplicityByBase: -β₀*(c×b) + β₁*(b×d)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase => {
                let bi = add_base(&mut b, 0);
                let c = add_base(&mut b, 1);
                let d = add_base(&mut b, 2);
                b.push_unified_quadratic(c, bi, neg_bc0());
                b.push_unified_quadratic(bi, d, bc1());
                b.push_c0_only_linear(d, bc0());
                b.push_constant(bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(c, neg_bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
                b.push_c0_only_linear(d, bc1_gamma(BF::ONE, 1));
                b.push_constant(bc1_gamma(BF::ONE, 2));
            }

            // ---------------------------------------------------------------
            // LookupExtMinusMultiplicityByExt: c bf, b/d ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt => {
                let c = add_base(&mut b, 0);
                let bi = add_ext(&mut b, 0);
                let d = add_ext(&mut b, 1);
                b.push_unified_quadratic(c, bi, neg_bc0());
                b.push_unified_quadratic(bi, d, bc1());
                b.push_c0_only_linear(d, bc0());
                b.push_constant(bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(c, neg_bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
                b.push_c0_only_linear(d, bc1_gamma(BF::ONE, 1));
                b.push_constant(bc1_gamma(BF::ONE, 2));
            }

            // ---------------------------------------------------------------
            // LookupUnbalanced: d base, a/b ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupUnbalanced => {
                let d = add_base(&mut b, 0);
                let a = add_ext(&mut b, 0);
                let bi = add_ext(&mut b, 1);
                b.push_unified_quadratic(d, a, bc0());
                b.push_unified_quadratic(d, bi, bc1());
                b.push_c0_only_linear(bi, bc0());
                b.push_c0_only_linear(a, bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
            }

            // ---------------------------------------------------------------
            // LookupUnbalancedExtension: d/a/b ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupUnbalancedExtension => {
                let a = add_ext(&mut b, 0);
                let bi = add_ext(&mut b, 1);
                let d = add_ext(&mut b, 2);
                b.push_unified_quadratic(d, a, bc0());
                b.push_unified_quadratic(d, bi, bc1());
                b.push_c0_only_linear(bi, bc0());
                b.push_c0_only_linear(a, bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
            }

            // ---------------------------------------------------------------
            // LookupWithCachedDensAndSetup: a/c base, b/d ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup => {
                let a = add_base(&mut b, 0);
                let bi = add_ext(&mut b, 0);
                let c = add_base(&mut b, 1);
                let d = add_ext(&mut b, 1);
                b.push_unified_quadratic(a, d, bc0());
                b.push_unified_quadratic(c, bi, neg_bc0());
                b.push_unified_quadratic(bi, d, bc1());
                b.push_c0_only_linear(a, bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(c, neg_bc0_gamma(BF::ONE, 1));
                b.push_c0_only_linear(bi, bc1_gamma(BF::ONE, 1));
                b.push_c0_only_linear(d, bc1_gamma(BF::ONE, 1));
                b.push_constant(bc1_gamma(BF::ONE, 2));
            }

            // ---------------------------------------------------------------
            // Constraint gates: quadratic → unified_quadratic, linear → c0_only_linear
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic => {
                emit_continuation_constraint_gate(&mut b, gate, p0);
            }

            GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput => {
                emit_continuation_constraint_gate(&mut b, gate, p0);
            }

            GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair => {
                emit_continuation_constraint_gate(&mut b, gate, p0);
            }

            // ---------------------------------------------------------------
            // Cross-product gates: all lhs×rhs pairs → unified_quadratic
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches => {
                emit_continuation_cross_product_gate(&mut b, gate, p0, 0);
            }

            // ---------------------------------------------------------------
            // Materialize: linear_form terms → unified_linear
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression => {
                emit_continuation_materialize_gate(&mut b, gate, p0, 0);
            }

            // ---------------------------------------------------------------
            // LookupPairFromBase/Vector: cross-product on β₁
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs
            | GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs => {
                // num = b + d (β₀), den = b * d (β₁)
                emit_continuation_linear_form(&mut b, gate, p0, false, false, 0);
                emit_continuation_linear_form(&mut b, gate, p0, false, true, 0);
                emit_continuation_cross_product_gate(&mut b, gate, p1, 0);
            }

            GpuGKRMainLayerKernelKind::LookupExtPair => {
                let lhs = add_ext(&mut b, 0);
                let rhs = add_ext(&mut b, 1);
                b.push_unified_quadratic(lhs, rhs, bc1());
                b.push_c0_only_linear(lhs, bc0());
                b.push_c0_only_linear(rhs, bc0());
                b.push_constant(bc0_gamma(BF::from_u32_unchecked(2), 1));
                b.push_c0_only_linear(lhs, bc1_gamma(BF::ONE, 1));
                b.push_c0_only_linear(rhs, bc1_gamma(BF::ONE, 1));
                b.push_constant(bc1_gamma(BF::ONE, 2));
            }

            // ---------------------------------------------------------------
            // LookupWithDensAndSetupExpressions: a/c cached, b/d from linear forms
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions => {
                let a = add_base(&mut b, 0);
                let c = add_base(&mut b, 1);
                let offset = 2usize;
                emit_continuation_single_times_linear_form(
                    &mut b, gate, a, p0, false, true, offset,
                );
                emit_continuation_single_times_linear_form(
                    &mut b, gate, c, p0, true, false, offset,
                );
                emit_continuation_cross_product_gate(&mut b, gate, p1, offset);
            }

            // ---------------------------------------------------------------
            // LookupFromVectorInputWithSetup: c cached, b/d from linear forms
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup => {
                let c = add_base(&mut b, 0);
                let offset = 1usize;
                emit_continuation_single_times_linear_form(
                    &mut b, gate, c, p0, true, false, offset,
                );
                emit_continuation_linear_form(&mut b, gate, p0, false, true, offset);
                emit_continuation_cross_product_gate(&mut b, gate, p1, offset);
            }

            // ---------------------------------------------------------------
            // LookupUnbalancedPairWithVectorInputs: d from linear form, a/b ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs => {
                let a = add_ext(&mut b, 0);
                let bi = add_ext(&mut b, 1);
                emit_continuation_linear_form_times_ext(&mut b, gate, a, p0, false, 0);
                emit_continuation_linear_form_times_ext(&mut b, gate, bi, p1, false, 0);
                b.push_c0_only_linear(bi, bc0());
            }
        }
    }

    b.finish()
}

// ---------------------------------------------------------------------------
// Continuation constraint gate helpers
// ---------------------------------------------------------------------------

/// Emit terms for constraint gates in continuation rounds.
/// Quadratic constraint terms → unified_quadratic (always both c0 and c1).
/// Linear constraint terms → c0_only_linear (compact: c0 only; explicit: both).
/// Constant offset → constant term.
fn emit_continuation_constraint_gate<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    batch_power: u32,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            // Quadratic terms → unified_quadratic
            for qt in &tmpl.quadratic_terms {
                let lhs = b.add_source(
                    gate.base_inputs[qt.lhs as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.lhs as usize,
                );
                let rhs = b.add_source(
                    gate.base_inputs[qt.rhs as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.rhs as usize,
                );
                b.push_unified_quadratic(
                    lhs,
                    rhs,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![qt.challenge_terms.clone()],
                    },
                );
            }
            // Linear terms → c0_only_linear
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let src = b.add_source(
                    gate.base_inputs[lt.input as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize,
                );
                b.push_c0_only_linear(
                    src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![lt.challenge_terms.clone()],
                    },
                );
            }
            // Constant offset (from linear terms with sentinel input)
            if tmpl
                .linear_terms
                .iter()
                .any(|lt| lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL)
            {
                // The constant is encoded as a linear term with sentinel input;
                // its coefficient includes the challenge product.
                for lt in &tmpl.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone()],
                        });
                    }
                }
            }
            if !tmpl.constant_terms.is_empty() {
                b.push_constant(CoefficientRecipe {
                    batch_power,
                    negate: false,
                    immediate_factor: E::ONE,
                    immediate_recipe: ImmediateFactorRecipeStructural::one(),
                    prefactors: vec![tmpl.constant_terms.clone()],
                });
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for qt in &meta.quadratic_terms {
                let lhs = b.add_source(
                    gate.base_inputs[qt.lhs as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.lhs as usize,
                );
                let rhs = b.add_source(
                    gate.base_inputs[qt.rhs as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.rhs as usize,
                );
                b.push_unified_quadratic(
                    lhs,
                    rhs,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: qt.challenge,
                        immediate_recipe: qt.immediate_recipe.clone(),
                        prefactors: vec![],
                    },
                );
            }
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let src = b.add_source(
                    gate.base_inputs[lt.input as usize].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize,
                );
                b.push_c0_only_linear(
                    src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: lt.challenge,
                        immediate_recipe: lt.immediate_recipe.clone(),
                        prefactors: vec![],
                    },
                );
            }
            // Constant offset
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: lt.challenge,
                        immediate_recipe: lt.immediate_recipe.clone(),
                        prefactors: vec![],
                    });
                }
            }
            if !meta.constant_offset.is_zero() {
                b.push_constant(CoefficientRecipe {
                    batch_power,
                    negate: false,
                    immediate_factor: meta.constant_offset,
                    immediate_recipe: meta.constant_offset_recipe.clone(),
                    prefactors: vec![],
                });
            }
        }
        None => panic!("constraint gate requires metadata"),
    }
}

/// Emit unified_quadratic terms for cross-product gates.
fn emit_continuation_cross_product_gate<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    batch_power: u32,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            let mut quad_terms = Vec::new();
            let mut quad_consts = Vec::new();
            for qt in &tmpl.quadratic_terms {
                if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    quad_consts.push(qt.challenge_terms.clone());
                } else {
                    quad_terms.push(qt);
                }
            }
            let mut lin_terms = Vec::new();
            let mut lin_consts = Vec::new();
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    lin_consts.push(lt.challenge_terms.clone());
                } else {
                    lin_terms.push(lt);
                }
            }

            for qt in &quad_terms {
                let lhs = b.add_source(
                    gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.lhs as usize + base_input_offset,
                );
                for lt in &lin_terms {
                    let rhs = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    b.push_unified_quadratic(
                        lhs,
                        rhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![
                                qt.challenge_terms.clone(),
                                lt.challenge_terms.clone(),
                            ],
                        },
                    );
                }
                for lc in &lin_consts {
                    b.push_c0_only_linear(
                        lhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![qt.challenge_terms.clone(), lc.clone()],
                        },
                    );
                }
            }

            for lt in &lin_terms {
                let rhs = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                for qc in &quad_consts {
                    b.push_c0_only_linear(
                        rhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone(), qc.clone()],
                        },
                    );
                }
            }

            for qc in &quad_consts {
                for lc in &lin_consts {
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![qc.clone(), lc.clone()],
                    });
                }
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            let mut quad_terms = Vec::new();
            let mut quad_consts = Vec::new();
            for qt in &meta.quadratic_terms {
                if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    quad_consts.push((qt.challenge, qt.immediate_recipe.clone()));
                } else {
                    quad_terms.push(qt);
                }
            }
            let mut lin_terms = Vec::new();
            let mut lin_consts = Vec::new();
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    lin_consts.push((lt.challenge, lt.immediate_recipe.clone()));
                } else {
                    lin_terms.push(lt);
                }
            }

            for qt in &quad_terms {
                let lhs = b.add_source(
                    gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start as usize,
                    gate.gate_idx,
                    false,
                    qt.lhs as usize + base_input_offset,
                );
                for lt in &lin_terms {
                    let rhs = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    let mut coeff = qt.challenge;
                    coeff.mul_assign(&lt.challenge);
                    let recipe = qt.immediate_recipe.mul(&lt.immediate_recipe);
                    b.push_unified_quadratic(
                        lhs,
                        rhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
                for (lc, lc_recipe) in &lin_consts {
                    let mut coeff = qt.challenge;
                    coeff.mul_assign(lc);
                    let recipe = qt.immediate_recipe.mul(lc_recipe);
                    b.push_c0_only_linear(
                        lhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            }

            for lt in &lin_terms {
                let rhs = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                for (qc, qc_recipe) in &quad_consts {
                    let mut coeff = lt.challenge;
                    coeff.mul_assign(qc);
                    let recipe = lt.immediate_recipe.mul(qc_recipe);
                    b.push_c0_only_linear(
                        rhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            }

            for (qc, qc_recipe) in &quad_consts {
                for (lc, lc_recipe) in &lin_consts {
                    let mut coeff = *qc;
                    coeff.mul_assign(lc);
                    let recipe = qc_recipe.mul(lc_recipe);
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: coeff,
                        immediate_recipe: recipe,
                        prefactors: vec![],
                    });
                }
            }
        }
        None => panic!("cross-product gate requires metadata"),
    }
}

/// Emit unified_linear terms for materialize gates.
fn emit_continuation_materialize_gate<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    batch_power: u32,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![lt.challenge_terms.clone()],
                    });
                    continue;
                }
                let src = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                b.push_unified_linear(
                    src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![lt.challenge_terms.clone()],
                    },
                );
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: lt.challenge,
                        immediate_recipe: lt.immediate_recipe.clone(),
                        prefactors: vec![],
                    });
                    continue;
                }
                let src = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                b.push_unified_linear(
                    src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: lt.challenge,
                        immediate_recipe: lt.immediate_recipe.clone(),
                        prefactors: vec![],
                    },
                );
            }
        }
        None => panic!("materialize gate requires metadata"),
    }
}

/// Emit unified_quadratic: cached_src × linear_form_term for each term.
/// When `use_linear_terms` is true, iterates `linear_terms`; otherwise `quadratic_terms` (using lhs).
fn emit_continuation_single_times_linear_form<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    cached_src: u32,
    batch_power: u32,
    negate: bool,
    use_linear_terms: bool,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            if use_linear_terms {
                for lt in &tmpl.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate,
                                immediate_factor: E::ONE,
                                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                                prefactors: vec![lt.challenge_terms.clone()],
                            },
                        );
                        continue;
                    }
                    let other = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    b.push_unified_quadratic(
                        cached_src,
                        other,
                        CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone()],
                        },
                    );
                }
            } else {
                for qt in &tmpl.quadratic_terms {
                    if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate,
                                immediate_factor: E::ONE,
                                immediate_recipe: ImmediateFactorRecipeStructural::one(),
                                prefactors: vec![qt.challenge_terms.clone()],
                            },
                        );
                        continue;
                    }
                    let other = b.add_source(
                        gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        qt.lhs as usize + base_input_offset,
                    );
                    b.push_unified_quadratic(
                        cached_src,
                        other,
                        CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![qt.challenge_terms.clone()],
                        },
                    );
                }
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            if use_linear_terms {
                for lt in &meta.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        let mut coeff = lt.challenge;
                        let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate: false,
                                immediate_factor: coeff,
                                immediate_recipe: recipe,
                                prefactors: vec![],
                            },
                        );
                        continue;
                    }
                    let other = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    let mut coeff = lt.challenge;
                    let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_unified_quadratic(
                        cached_src,
                        other,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            } else {
                for qt in &meta.quadratic_terms {
                    if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        let mut coeff = qt.challenge;
                        let recipe = immediate_recipe_with_negation(&qt.immediate_recipe, negate);
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate: false,
                                immediate_factor: coeff,
                                immediate_recipe: recipe,
                                prefactors: vec![],
                            },
                        );
                        continue;
                    }
                    let other = b.add_source(
                        gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        qt.lhs as usize + base_input_offset,
                    );
                    let mut coeff = qt.challenge;
                    let recipe = immediate_recipe_with_negation(&qt.immediate_recipe, negate);
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_unified_quadratic(
                        cached_src,
                        other,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            }
        }
        None => panic!("gate requires metadata"),
    }
}

/// Emit c0-only linear terms for a no-cache linear form (including constants).
fn emit_continuation_linear_form<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    batch_power: u32,
    negate: bool,
    use_linear_terms: bool,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            if use_linear_terms {
                for lt in &tmpl.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone()],
                        });
                        continue;
                    }
                    let src = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    b.push_c0_only_linear(
                        src,
                        CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone()],
                        },
                    );
                }
            } else {
                for qt in &tmpl.quadratic_terms {
                    if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![qt.challenge_terms.clone()],
                        });
                        continue;
                    }
                    let src = b.add_source(
                        gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        qt.lhs as usize + base_input_offset,
                    );
                    b.push_c0_only_linear(
                        src,
                        CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![qt.challenge_terms.clone()],
                        },
                    );
                }
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            if use_linear_terms {
                for lt in &meta.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        let mut coeff = lt.challenge;
                        let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        });
                        continue;
                    }
                    let src = b.add_source(
                        gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        lt.input as usize + base_input_offset,
                    );
                    let mut coeff = lt.challenge;
                    let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            } else {
                for qt in &meta.quadratic_terms {
                    if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        let mut coeff = qt.challenge;
                        let recipe = immediate_recipe_with_negation(&qt.immediate_recipe, negate);
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        });
                        continue;
                    }
                    let src = b.add_source(
                        gate.base_inputs[qt.lhs as usize + base_input_offset].this_layer_start
                            as usize,
                        gate.gate_idx,
                        false,
                        qt.lhs as usize + base_input_offset,
                    );
                    let mut coeff = qt.challenge;
                    let recipe = immediate_recipe_with_negation(&qt.immediate_recipe, negate);
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                }
            }
        }
        None => panic!("gate requires metadata"),
    }
}

/// Emit unified_quadratic: linear_form_term × ext_source for each term.
fn emit_continuation_linear_form_times_ext<E: Field>(
    b: &mut FlatContinuationDescriptionBuilder<E>,
    gate: &PreparedGateForFlatContinuationPlan<'_, E>,
    ext_src: u32,
    batch_power: u32,
    negate: bool,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    b.push_c0_only_linear(
                        ext_src,
                        CoefficientRecipe {
                            batch_power,
                            negate,
                            immediate_factor: E::ONE,
                            immediate_recipe: ImmediateFactorRecipeStructural::one(),
                            prefactors: vec![lt.challenge_terms.clone()],
                        },
                    );
                    continue;
                }
                let bf_src = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                b.push_unified_quadratic(
                    bf_src,
                    ext_src,
                    CoefficientRecipe {
                        batch_power,
                        negate,
                        immediate_factor: E::ONE,
                        immediate_recipe: ImmediateFactorRecipeStructural::one(),
                        prefactors: vec![lt.challenge_terms.clone()],
                    },
                );
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    let mut coeff = lt.challenge;
                    let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        ext_src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
                            immediate_recipe: recipe,
                            prefactors: vec![],
                        },
                    );
                    continue;
                }
                let bf_src = b.add_source(
                    gate.base_inputs[lt.input as usize + base_input_offset].this_layer_start
                        as usize,
                    gate.gate_idx,
                    false,
                    lt.input as usize + base_input_offset,
                );
                let mut coeff = lt.challenge;
                let recipe = immediate_recipe_with_negation(&lt.immediate_recipe, negate);
                if negate {
                    Field::negate(&mut coeff);
                }
                b.push_unified_quadratic(
                    bf_src,
                    ext_src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: coeff,
                        immediate_recipe: recipe,
                        prefactors: vec![],
                    },
                );
            }
        }
        None => panic!("gate requires metadata"),
    }
}

// ---------------------------------------------------------------------------
// Continuation kernel declarations and launch
// ---------------------------------------------------------------------------

// Eval recipes kernel for continuation coefficients. Each challenge is read
// from its own device pointer (mirrors the round-0 kernel signature).
cuda_kernel_signature_arguments_and_function!(
    GpuFlatContEvalRecipes<T>,
    batch_base: *const T,
    lookup_mul: *const T,
    lookup_add: *const T,
    ext_challenges: *const T,
    desc: GpuFlatRecipeEvalDesc,
    coefficients: *mut T,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_continuation_eval_recipes_e4_kernel(
        batch_base: *const E4,
        lookup_mul: *const E4,
        lookup_add: *const E4,
        ext_challenges: *const E4,
        desc: GpuFlatRecipeEvalDesc,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

// ---------------------------------------------------------------------------
// Launch functions
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// __constant__ symbol address for continuation coefficients
// ---------------------------------------------------------------------------

extern "C" {
    static ab_gkr_flat_continuation_coefficients: [E4; FLAT_CONT_CONST_MAX];
}

pub(in crate::prover::gkr) fn get_constant_continuation_coefficients_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    // SAFETY: ab_gkr_flat_continuation_coefficients is a valid __constant__ symbol
    // defined in main_backward_round3_compute_coeff.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_flat_continuation_coefficients as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_flat_continuation_coefficients");
    ptr as *mut E4
}

// ---------------------------------------------------------------------------
// Eval recipes launch for continuation
// ---------------------------------------------------------------------------

pub(in crate::prover::gkr) fn eval_continuation_recipes_e4(
    batch_base: *const E4,
    lookup_mul: *const E4,
    lookup_add: *const E4,
    ext_challenges: *const E4,
    desc: &GpuFlatRecipeEvalDesc,
    num_recipes: usize,
    coefficients: *mut E4,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
    use era_cudart::execution::CudaLaunchConfig;

    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuFlatContEvalRecipesArguments::new(
        batch_base,
        lookup_mul,
        lookup_add,
        ext_challenges,
        *desc,
        coefficients,
        num_recipes as u32,
    );
    GpuFlatContEvalRecipesFunction(ab_gkr_flat_continuation_eval_recipes_e4_kernel)
        .launch(&config, &args)
}
