//! Flattened GKR backward pass round 0 kernel.
//!
//! Instead of a 20-way switch on gate kind, this compiles every gate in the
//! layer into flat arrays of linear/quadratic terms. The structural part
//! (source table + term pairs) is passed as `__grid_constant__`, while the
//! challenge-dependent coefficients live in a separate device buffer filled
//! at schedule time via a stream callback.

use std::collections::HashMap;

use field::Field;

use crate::primitives::field::E4;
use crate::prover::gkr::immediate_factors::{
    ImmediateFactorInterner, ImmediateFactorRecipeStructural,
};

use super::backward_flat_compact::{
    build_backing_ranges, pack_flat_round0_source_real, pack_flat_round0_source_virtual,
    resolve_backing_for_pointer, BackingRange, FlatRound0BuildPlanCompact,
    GpuFlatRound0StaticDescCompact,
};
use super::backward_kernels::{
    GpuGKRMainLayerConstraintMetadataSource, GpuGKRMainLayerConstraintTemplate,
    GpuGKRMainLayerKernelKind, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::{
    GpuBaseFieldPolySource, GpuExtensionFieldPolyInitialSource, GpuGKRStorage,
    GpuSumcheckRound0LaunchDescriptors,
};
use crate::primitives::field::BF;

mod continuation;

pub(super) use continuation::*;

// ---------------------------------------------------------------------------
// Constants (must match flat_backward.cuh)
// ---------------------------------------------------------------------------

// Must match flat_backward.cuh.
pub(super) const FLAT_ROUND0_CONST_MAX: usize = 512;
pub(super) const FLAT_ROUND0_MAX_SOURCES: usize = 1280;
pub(super) const FLAT_ROUND0_MAX_C0_BF: usize = 128;
pub(super) const FLAT_ROUND0_MAX_C0_EXT: usize = 512;
pub(super) const FLAT_ROUND0_MAX_C1_BF_BF: usize = 4096;
pub(super) const FLAT_ROUND0_MAX_C1_E4_E4: usize = 512;
pub(super) const FLAT_ROUND0_MAX_C1_BF_E4: usize = 512;
pub(super) const FLAT_ROUND0_MAX_C1_LINEAR: usize = 128;

// ---------------------------------------------------------------------------
// Static description types (mirror CUDA structs, no field type parameter)
// ---------------------------------------------------------------------------

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(super) struct GpuFlatC0Ref {
    pub(super) source_idx: u16,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(super) struct GpuFlatC1Pair {
    pub(super) source_a: u16,
    pub(super) source_b: u16,
}

/// Term types for the unified term array.
pub(super) const TERM_TYPE_CONSTANT: u16 = 0;
pub(super) const TERM_TYPE_C0_ONLY_LINEAR: u16 = 1;
pub(super) const TERM_TYPE_UNIFIED_QUADRATIC: u16 = 2;
pub(super) const TERM_TYPE_UNIFIED_LINEAR: u16 = 3;

/// Unified term entry: mixes all term types in a single array, sorted
/// by source-group affinity. Each term carries its type tag and an index into
/// the coefficient array so the coefficient layout doesn't need to change.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(super) struct GpuFlatUnifiedTerm {
    pub(super) source_a: u16,
    pub(super) source_b: u16,
    pub(super) term_type: u16,
    pub(super) coeff_idx: u16,
}

// ---------------------------------------------------------------------------
// Coefficient recipes
// ---------------------------------------------------------------------------

use super::backward_kernels::GpuGKRMainLayerConstraintChallengeTerm;

/// Describes how to compute a single term's coefficient at runtime.
///
/// The coefficient is: `base^batch_power * immediate_factor * Π(prefactor_i)`,
/// negated if `negate` is true.
///
/// - `immediate_factor`: known at build time (constraint coefficient, sign, etc.)
/// - `prefactors`: each evaluated at runtime via `evaluate_constraint_prefactor`
#[allow(dead_code)]
#[derive(Clone)]
pub(super) struct CoefficientRecipe<E> {
    pub(super) batch_power: u32,
    pub(super) negate: bool,
    /// Product factor known at build time (default: E::ONE).
    ///
    /// TODO(perf): many gates promote a cs-side `u32` coefficient into `E`
    /// here, paying `E * BF * BF` per row instead of `BF * BF * BF`. See
    /// [`docs/backward_immediate_factor_encoding.md`](../../../docs/backward_immediate_factor_encoding.md)
    /// for the design note and viable encodings.
    pub(super) immediate_factor: E,
    pub(super) immediate_recipe: ImmediateFactorRecipeStructural,
    /// 0..2 additional challenge prefactors evaluated at runtime.
    pub(super) prefactors: Vec<Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
}

pub(super) fn immediate_recipe_with_negation(
    recipe: &ImmediateFactorRecipeStructural,
    negate: bool,
) -> ImmediateFactorRecipeStructural {
    if negate {
        recipe.negated()
    } else {
        recipe.clone()
    }
}

// ---------------------------------------------------------------------------
// Build plan: static desc + recipes, produced at prepare time
// ---------------------------------------------------------------------------

impl<E: Field + field::FieldExtension<BF>> FlatRound0BuildPlanCompact<E> {
    pub(super) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }
}

// ---------------------------------------------------------------------------
// Kernel declaration and launch
// ---------------------------------------------------------------------------

use era_cudart::result::CudaResultWrap;

use crate::primitives::utils::{
    compute_minimal_carveout, set_shared_carveout, smem_pool_bytes_per_sm,
};

/// One-time setup: configure shared memory carveout for flat kernels.
/// Kernels without shared memory get 0% (maximize L1).
/// The unified tiled kernels get a minimal carveout (just enough for their
/// static shared memory at max occupancy), leaving the rest for L1.
pub(in crate::prover) fn configure_flat_kernel_cache_preference() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        use super::backward_flat_compact::{
            ab_gkr_main_round0_flat_compact_e4_kernel,
            ab_gkr_main_round0_flat_constant_compact_e4_kernel,
            ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel,
            ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel,
            ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel,
            ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel,
        };
        // Kernels with zero shared memory → 0% carveout → maximize L1.
        let no_smem_kernels: &[*const std::ffi::c_void] = &[
            ab_gkr_main_round0_flat_compact_e4_kernel as *const std::ffi::c_void,
            ab_gkr_main_round0_flat_constant_compact_e4_kernel as *const std::ffi::c_void,
        ];
        for &kernel in no_smem_kernels {
            set_shared_carveout(kernel, 0);
        }

        // Unified tiled kernels: compute the minimal carveout from the device's
        // configurable shared/L1 pool size and each kernel's actual shared memory
        // footprint at max occupancy.
        let pool_bytes = smem_pool_bytes_per_sm();
        let block_size = 128i32; // all unified tiled kernels use 128 threads
        for kernel in [
            ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel
                as *const std::ffi::c_void,
            ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel as *const std::ffi::c_void,
            ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel
                as *const std::ffi::c_void,
            ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel
                as *const std::ffi::c_void,
        ] {
            let pct = compute_minimal_carveout(kernel, block_size, pool_bytes);
            set_shared_carveout(kernel, pct);
        }
    });
}

// ---------------------------------------------------------------------------
// __constant__ symbol address
// ---------------------------------------------------------------------------

use era_cudart_sys::cudaGetSymbolAddress;
use std::ffi::c_void;

extern "C" {
    static ab_gkr_flat_round0_coefficients: [E4; FLAT_ROUND0_CONST_MAX];
}

/// Get the device address of the `__constant__` coefficient symbol.
/// This is a trivial host-side symbol lookup (no GPU blocking).
pub(super) fn get_constant_coefficients_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    // SAFETY: ab_gkr_flat_round0_coefficients is a valid __constant__ symbol
    // defined in main_backward_round0_flat.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_flat_round0_coefficients as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_flat_round0_coefficients");
    ptr as *mut E4
}

// ---------------------------------------------------------------------------
// Recipe compilation for device
// ---------------------------------------------------------------------------

use super::backward_kernels::GpuGKRMainLayerDeferredChallengeSource;
use crate::prover::gkr::eval_recipes::{
    GpuFlatRecipeEvalDesc, GpuPrefactorTerm, GpuRecipeHeader, FLAT_IMMEDIATE_MAX_MONOMIALS,
    FLAT_IMMEDIATE_MAX_RECIPES, FLAT_RECIPE_MAX_HEADERS, FLAT_RECIPE_MAX_TERMS,
};

/// Compiled recipe buffer ready for device upload.
#[allow(dead_code)]
pub(super) struct CompiledRecipeBuffers {
    pub(super) desc: Box<GpuFlatRecipeEvalDesc>,
    pub(super) num_recipes: usize,
    pub(super) num_terms: usize,
    pub(super) num_immediate_recipes: usize,
    pub(super) num_immediate_monomials: usize,
}

/// Compile `CoefficientRecipe` entries into the device-side format.
pub(super) fn compile_recipes_for_device<E: Field + field::FieldExtension<BF>>(
    recipes: &[CoefficientRecipe<E>],
) -> CompiledRecipeBuffers {
    assert!(
        recipes.len() <= FLAT_RECIPE_MAX_HEADERS,
        "flat recipe count {} exceeds cap {}",
        recipes.len(),
        FLAT_RECIPE_MAX_HEADERS
    );
    let mut desc = Box::<GpuFlatRecipeEvalDesc>::default();
    let mut terms = Vec::new();
    let mut immediate_interner = ImmediateFactorInterner::new();

    for (idx, recipe) in recipes.iter().enumerate() {
        assert!(
            recipe.batch_power <= u16::MAX as u32,
            "flat recipe batch power {} exceeds u16",
            recipe.batch_power
        );
        let terms_offset = terms.len();
        assert!(
            terms_offset <= u16::MAX as usize,
            "flat recipe terms offset {} exceeds u16",
            terms_offset
        );
        let mut group_counts = [0u8; 2];

        for (g, group) in recipe.prefactors.iter().enumerate() {
            assert!(g < 2, "at most 2 prefactor groups per recipe");
            assert!(
                group.len() <= u8::MAX as usize,
                "flat recipe prefactor group has too many terms"
            );
            group_counts[g] = group.len() as u8;
            for term in group {
                let source = match term.source {
                    GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => 0u8,
                    GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => 1u8,
                };
                assert!(
                    term.power <= u8::MAX as u32,
                    "flat recipe prefactor power {} exceeds u8",
                    term.power
                );
                terms.push(GpuPrefactorTerm {
                    coeff: term.coeff,
                    source,
                    power: term.power as u8,
                    _pad: 0,
                });
            }
        }
        assert!(
            terms.len() <= FLAT_RECIPE_MAX_TERMS,
            "flat recipe term count {} exceeds cap {}",
            terms.len(),
            FLAT_RECIPE_MAX_TERMS
        );

        let immediate_recipe = if recipe.negate {
            recipe.immediate_recipe.negated()
        } else {
            recipe.immediate_recipe.clone()
        };
        let immediate_idx = immediate_interner.intern(immediate_recipe);

        desc.headers[idx] = GpuRecipeHeader {
            batch_power: recipe.batch_power as u16,
            group_count_0: group_counts[0],
            group_count_1: group_counts[1],
            terms_offset: terms_offset as u16,
            immediate_idx,
        };
    }

    let (immediate_headers, immediate_monomials) = immediate_interner.materialize();
    assert!(
        immediate_headers.len() <= FLAT_IMMEDIATE_MAX_RECIPES,
        "flat immediate recipe count {} exceeds cap {}",
        immediate_headers.len(),
        FLAT_IMMEDIATE_MAX_RECIPES
    );
    assert!(
        immediate_monomials.len() <= FLAT_IMMEDIATE_MAX_MONOMIALS,
        "flat immediate monomial count {} exceeds cap {}",
        immediate_monomials.len(),
        FLAT_IMMEDIATE_MAX_MONOMIALS
    );
    desc.terms[..terms.len()].copy_from_slice(&terms);
    desc.immediate_recipes[..immediate_headers.len()].copy_from_slice(&immediate_headers);
    desc.immediate_monomials[..immediate_monomials.len()].copy_from_slice(&immediate_monomials);

    CompiledRecipeBuffers {
        desc,
        num_recipes: recipes.len(),
        num_terms: terms.len(),
        num_immediate_recipes: immediate_headers.len(),
        num_immediate_monomials: immediate_monomials.len(),
    }
}

// ---------------------------------------------------------------------------
// Source table builder (compact: emits u16-packed (slot, poly_idx) per source
// directly via the storage's per-(layer, class) consolidated backings)
// ---------------------------------------------------------------------------

pub(super) struct FlatDescriptionBuilder<'s, E: Field> {
    desc: Box<GpuFlatRound0StaticDescCompact>,
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
    pub(super) fn new(storage: &'s GpuGKRStorage<BF, E>) -> Self {
        Self {
            desc: Box::new(GpuFlatRound0StaticDescCompact::default()),
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
        self.desc.sources[idx as usize] =
            super::backward_kernels::GpuGKRSourceRecord::source_only(packed);
        self.desc.num_sources = idx + 1;
        self.source_map.insert(packed, idx);
        idx
    }

    pub(super) fn add_bf_source<B>(&mut self, src: &GpuBaseFieldPolySource<B>) -> u32 {
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

    pub(super) fn add_ext_source(&mut self, src: &GpuExtensionFieldPolyInitialSource<E>) -> u32 {
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

    pub(super) fn push_c0_bf(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_c0_bf as usize;
        assert!(i < FLAT_ROUND0_MAX_C0_BF, "flat round0: c0_bf overflow");
        self.desc.c0_bf[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c0_bf += 1;
        self.recipes_c0_bf.push(recipe);
    }

    pub(super) fn push_c0_ext(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_c0_ext as usize;
        assert!(i < FLAT_ROUND0_MAX_C0_EXT, "flat round0: c0_ext overflow");
        self.desc.c0_ext[i] = GpuFlatC0Ref {
            source_idx: source_idx as u16,
        };
        self.desc.num_c0_ext += 1;
        self.recipes_c0_ext.push(recipe);
    }

    pub(super) fn push_c1_bf_bf(
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

    pub(super) fn push_c1_e4_e4(
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

    pub(super) fn push_c1_bf_e4(
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

    pub(super) fn push_c1_linear(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
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

    pub(super) fn finish(self) -> FlatRound0BuildPlanCompact<E> {
        // Concatenate recipes in tier order to match kernel's *coeff++ traversal.
        let mut recipes = self.recipes_c0_bf;
        recipes.extend(self.recipes_c0_ext);
        recipes.extend(self.recipes_c1_bf_bf);
        recipes.extend(self.recipes_c1_e4_e4);
        recipes.extend(self.recipes_c1_bf_e4);
        recipes.extend(self.recipes_c1_linear);
        FlatRound0BuildPlanCompact {
            static_desc: self.desc,
            recipes,
        }
    }
}

// ---------------------------------------------------------------------------
// Gate decomposer
// ---------------------------------------------------------------------------

pub(super) const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;

/// Per-gate data needed for building the flat plan.
pub(super) struct PreparedGateForFlatPlan<'a, E> {
    pub(super) kind: GpuGKRMainLayerKernelKind,
    pub(super) round0: &'a GpuSumcheckRound0LaunchDescriptors<BF, E>,
    /// The power of `batch_challenge_base` assigned to this gate's first batch challenge.
    pub(super) batch_challenge_power_offset: u32,
    /// Constraint metadata source: Immediate (test) or Deferred (production).
    pub(super) constraint_source: Option<&'a GpuGKRMainLayerConstraintMetadataSource<E>>,
}

/// Build the flat plan from prepared gates. The returned plan carries the
/// compact `(slot, poly_idx)` source encoding directly — no separate
/// post-processing pass.
pub(super) fn build_flat_round0_plan<'s, E: Field>(
    gates: &[PreparedGateForFlatPlan<'_, E>],
    storage: &'s GpuGKRStorage<BF, E>,
) -> FlatRound0BuildPlanCompact<E> {
    let mut b = FlatDescriptionBuilder::<'s, E>::new(storage);

    for gate in gates {
        let r0 = gate.round0;
        let p0 = gate.batch_challenge_power_offset;
        let p1 = p0 + 1; // second batch challenge power (if gate uses 2)

        // Helpers for creating simple recipes (no constraint prefactors)
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

        match gate.kind {
            // ---------------------------------------------------------------
            // Copy gates: c0 = β₀ * output; c1 = 0
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::BaseCopy | GpuGKRMainLayerKernelKind::LinearBaseOutput => {
                let out = b.add_bf_source(&r0.base_field_outputs[0]);
                b.push_c0_bf(out, bc0());
            }

            GpuGKRMainLayerKernelKind::ExtCopy => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
            }

            // ---------------------------------------------------------------
            // Product: c0 = β₀ * output; c1 = β₀ * Δa * Δb
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::Product => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
                let a = b.add_ext_source(&r0.extension_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[1]);
                b.push_c1_e4_e4(a, bi, bc0());
            }

            // ---------------------------------------------------------------
            // MaskIdentity: c0 = β₀ * output; c1 = β₀ * Δmask(bf) * Δvalue(ext)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::MaskIdentity => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
                let mask = b.add_bf_source(&r0.base_field_inputs[0]);
                let val = b.add_ext_source(&r0.extension_field_inputs[0]);
                b.push_c1_bf_e4(mask, val, bc0());
            }

            // ---------------------------------------------------------------
            // LookupPair: c0 = β₀*num + β₁*den
            // c1 = β₀*(Δa·Δd + Δc·Δb) + β₁*(Δb·Δd)  [all ext]
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupPair => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let a = b.add_ext_source(&r0.extension_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[1]);
                let c = b.add_ext_source(&r0.extension_field_inputs[2]);
                let d = b.add_ext_source(&r0.extension_field_inputs[3]);
                b.push_c1_e4_e4(a, d, bc0());
                b.push_c1_e4_e4(c, bi, bc0());
                b.push_c1_e4_e4(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // LookupBasePair: c1 = β₁ * Δb * Δd  (num=0, b/d bf)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupBasePair => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let bi = b.add_bf_source(&r0.base_field_inputs[0]);
                let d = b.add_bf_source(&r0.base_field_inputs[1]);
                b.push_c1_bf_bf(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // LookupBaseMinusMultiplicityByBase: c1 = -β₀*(Δc·Δb) + β₁*(Δb·Δd)
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let bi = b.add_bf_source(&r0.base_field_inputs[0]);
                let c = b.add_bf_source(&r0.base_field_inputs[1]);
                let d = b.add_bf_source(&r0.base_field_inputs[2]);
                b.push_c1_bf_bf(c, bi, neg_bc0());
                b.push_c1_bf_bf(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // LookupExtMinusMultiplicityByExt: c is bf, b/d ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let c = b.add_bf_source(&r0.base_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[0]);
                let d = b.add_ext_source(&r0.extension_field_inputs[1]);
                b.push_c1_bf_e4(c, bi, neg_bc0());
                b.push_c1_e4_e4(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // LookupUnbalanced: d bf, a/b ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupUnbalanced => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let d = b.add_bf_source(&r0.base_field_inputs[0]);
                let a = b.add_ext_source(&r0.extension_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[1]);
                b.push_c1_bf_e4(d, a, bc0());
                b.push_c1_bf_e4(d, bi, bc1());
            }

            // ---------------------------------------------------------------
            // LookupUnbalancedExtension: d/a/b ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupUnbalancedExtension => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let a = b.add_ext_source(&r0.extension_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[1]);
                let d = b.add_ext_source(&r0.extension_field_inputs[2]);
                b.push_c1_e4_e4(d, a, bc0());
                b.push_c1_e4_e4(d, bi, bc1());
            }

            // ---------------------------------------------------------------
            // LookupWithCachedDensAndSetup: a/c bf, b/d ext
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let a = b.add_bf_source(&r0.base_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[0]);
                let c = b.add_bf_source(&r0.base_field_inputs[1]);
                let d = b.add_ext_source(&r0.extension_field_inputs[1]);
                b.push_c1_bf_e4(a, d, bc0());
                b.push_c1_bf_e4(c, bi, neg_bc0());
                b.push_c1_e4_e4(bi, d, bc1());
            }

            // ---------------------------------------------------------------
            // Gates with constraint metadata: EnforceConstraints, InitsAndTeardowns,
            // InitialGrandProduct, Materialize, Lookup*FromBase, LookupWithDensAndSetup,
            // LookupFromVectorInputWithSetup, LookupUnbalancedPairWithVectorInputs
            // ---------------------------------------------------------------
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic => {
                emit_constraint_gate(&mut b, gate, r0, p0);
            }

            GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput => {
                let out = b.add_bf_source(&r0.base_field_outputs[0]);
                b.push_c0_bf(out, bc0());
                emit_constraint_gate(&mut b, gate, r0, p0);
            }

            GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
                emit_constraint_gate(&mut b, gate, r0, p0);
            }

            GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
                emit_cross_product_gate(&mut b, gate, r0, p0, 0);
            }

            GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression => {
                let out = b.add_ext_source(&r0.extension_field_outputs[0]);
                b.push_c0_ext(out, bc0());
                emit_materialize_gate(&mut b, gate, r0, p0, 0);
            }

            GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs
            | GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                // c1 = β₁ * cross_product(quad_terms, linear_terms)
                emit_cross_product_gate(&mut b, gate, r0, p1, 0);
            }

            GpuGKRMainLayerKernelKind::LookupExtPair => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let lhs = b.add_ext_source(&r0.extension_field_inputs[0]);
                let rhs = b.add_ext_source(&r0.extension_field_inputs[1]);
                b.push_c1_e4_e4(lhs, rhs, bc1());
            }

            GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let a = b.add_bf_source(&r0.base_field_inputs[0]);
                let c = b.add_bf_source(&r0.base_field_inputs[1]);
                let offset = 2usize;
                // β₀ * a * d: a is cached, d = linear_form(linear_terms)
                emit_single_times_linear_form(&mut b, gate, r0, a, p0, false, true, offset);
                // -β₀ * c * b: c is cached, b = linear_form(quad_terms)
                emit_single_times_linear_form(&mut b, gate, r0, c, p0, true, false, offset);
                // β₁ * b * d cross product
                emit_cross_product_gate(&mut b, gate, r0, p1, offset);
            }

            GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let c = b.add_bf_source(&r0.base_field_inputs[0]);
                let offset = 1usize;
                // -β₀ * c * b
                emit_single_times_linear_form(&mut b, gate, r0, c, p0, true, false, offset);
                // β₁ * b * d cross product
                emit_cross_product_gate(&mut b, gate, r0, p1, offset);
            }

            GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs => {
                let out_num = b.add_ext_source(&r0.extension_field_outputs[0]);
                let out_den = b.add_ext_source(&r0.extension_field_outputs[1]);
                b.push_c0_ext(out_num, bc0());
                b.push_c0_ext(out_den, bc1());
                let a = b.add_ext_source(&r0.extension_field_inputs[0]);
                let bi = b.add_ext_source(&r0.extension_field_inputs[1]);
                // d = linear_form(linear_terms) [bf]
                // c1 = β₀*Δd*Δa + β₁*Δd*Δb
                emit_linear_form_times_ext(&mut b, gate, r0, a, p0, false, 0);
                emit_linear_form_times_ext(&mut b, gate, r0, bi, p1, false, 0);
            }
        }
    }

    b.finish()
}

// ---------------------------------------------------------------------------
// Constraint gate helpers
// ---------------------------------------------------------------------------

/// Emit c1 terms for gates that use quadratic constraint metadata directly.
/// c1 += β * Σ (constraint_quad[i].challenge * Δ(lhs) * Δ(rhs))
fn emit_constraint_gate<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    gate: &PreparedGateForFlatPlan<'_, E>,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    batch_power: u32,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for qt in &tmpl.quadratic_terms {
                let lhs = b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize]);
                let rhs = b.add_bf_source(&r0.base_field_inputs[qt.rhs as usize]);
                b.push_c1_bf_bf(
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
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for qt in &meta.quadratic_terms {
                let lhs = b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize]);
                let rhs = b.add_bf_source(&r0.base_field_inputs[qt.rhs as usize]);
                b.push_c1_bf_bf(
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
        }
        None => panic!("constraint gate requires metadata"),
    }
}

/// Emit c1 terms for cross-product gates: c1 += β * (Σ aᵢΔᵢ)(Σ bⱼΔⱼ)
fn emit_cross_product_gate<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    gate: &PreparedGateForFlatPlan<'_, E>,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    batch_power: u32,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for qt in &tmpl.quadratic_terms {
                if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let lhs =
                    b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize + base_input_offset]);
                for lt in &tmpl.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        continue;
                    }
                    let rhs = b.add_bf_source(
                        &r0.base_field_inputs[lt.input as usize + base_input_offset],
                    );
                    b.push_c1_bf_bf(
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
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for qt in &meta.quadratic_terms {
                if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let lhs =
                    b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize + base_input_offset]);
                for lt in &meta.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        continue;
                    }
                    let rhs = b.add_bf_source(
                        &r0.base_field_inputs[lt.input as usize + base_input_offset],
                    );
                    let mut coeff = qt.challenge;
                    coeff.mul_assign(&lt.challenge);
                    let recipe = qt.immediate_recipe.mul(&lt.immediate_recipe);
                    b.push_c1_bf_bf(
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
            }
        }
        None => panic!("cross-product gate requires metadata"),
    }
}

/// Emit c1 terms for Materialize gates: c1 += β * Σ (lt.challenge * Δ(input))
fn emit_materialize_gate<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    gate: &PreparedGateForFlatPlan<'_, E>,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    batch_power: u32,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let src =
                    b.add_bf_source(&r0.base_field_inputs[lt.input as usize + base_input_offset]);
                b.push_c1_linear(
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
                    continue;
                }
                let src =
                    b.add_bf_source(&r0.base_field_inputs[lt.input as usize + base_input_offset]);
                b.push_c1_linear(
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

/// Emit terms: β * Σ(linear_form_terms_j · Δⱼ) * Δ(cached_src)
/// where cached_src is bf and linear_form terms produce bf deltas.
/// `use_linear_terms`: true = iterate linear_terms, false = iterate quadratic_terms
fn emit_single_times_linear_form<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    gate: &PreparedGateForFlatPlan<'_, E>,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    cached_src: u32,
    batch_power: u32,
    negate: bool,
    use_linear_terms: bool,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            if use_linear_terms {
                emit_single_times_linear_form_deferred_linear(
                    b,
                    tmpl,
                    r0,
                    cached_src,
                    batch_power,
                    negate,
                    base_input_offset,
                );
            } else {
                emit_single_times_linear_form_deferred_quad(
                    b,
                    tmpl,
                    r0,
                    cached_src,
                    batch_power,
                    negate,
                    base_input_offset,
                );
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            if use_linear_terms {
                for lt in &meta.linear_terms {
                    if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        continue;
                    }
                    let form_src = b.add_bf_source(
                        &r0.base_field_inputs[lt.input as usize + base_input_offset],
                    );
                    let mut coeff = lt.challenge;
                    let mut recipe = lt.immediate_recipe.clone();
                    if negate {
                        Field::negate(&mut coeff);
                        recipe = recipe.negated();
                    }
                    b.push_c1_bf_bf(
                        cached_src,
                        form_src,
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
                        continue;
                    }
                    let form_src =
                        b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize + base_input_offset]);
                    let mut coeff = qt.challenge;
                    let mut recipe = qt.immediate_recipe.clone();
                    if negate {
                        Field::negate(&mut coeff);
                        recipe = recipe.negated();
                    }
                    b.push_c1_bf_bf(
                        cached_src,
                        form_src,
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

fn emit_single_times_linear_form_deferred_linear<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    tmpl: &GpuGKRMainLayerConstraintTemplate,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    cached_src: u32,
    batch_power: u32,
    negate: bool,
    base_input_offset: usize,
) {
    for lt in &tmpl.linear_terms {
        if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
            continue;
        }
        let form_src =
            b.add_bf_source(&r0.base_field_inputs[lt.input as usize + base_input_offset]);
        b.push_c1_bf_bf(
            cached_src,
            form_src,
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

fn emit_single_times_linear_form_deferred_quad<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    tmpl: &GpuGKRMainLayerConstraintTemplate,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    cached_src: u32,
    batch_power: u32,
    negate: bool,
    base_input_offset: usize,
) {
    for qt in &tmpl.quadratic_terms {
        if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
            continue;
        }
        let form_src = b.add_bf_source(&r0.base_field_inputs[qt.lhs as usize + base_input_offset]);
        b.push_c1_bf_bf(
            cached_src,
            form_src,
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

/// Emit terms: β * Σ(linear_form_terms_j · Δⱼ_bf) * Δ(ext_src)
fn emit_linear_form_times_ext<E: Field>(
    b: &mut FlatDescriptionBuilder<'_, E>,
    gate: &PreparedGateForFlatPlan<'_, E>,
    r0: &GpuSumcheckRound0LaunchDescriptors<BF, E>,
    ext_src: u32,
    batch_power: u32,
    negate: bool,
    base_input_offset: usize,
) {
    match gate.constraint_source {
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(ref tmpl)) => {
            for lt in &tmpl.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    continue;
                }
                let bf_src =
                    b.add_bf_source(&r0.base_field_inputs[lt.input as usize + base_input_offset]);
                b.push_c1_bf_e4(
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
                    continue;
                }
                let bf_src =
                    b.add_bf_source(&r0.base_field_inputs[lt.input as usize + base_input_offset]);
                let mut coeff = lt.challenge;
                let mut recipe = lt.immediate_recipe.clone();
                if negate {
                    Field::negate(&mut coeff);
                    recipe = recipe.negated();
                }
                b.push_c1_bf_e4(
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

// ===========================================================================
// Flat continuation rounds (rounds 1, 2, 3+)
// ===========================================================================

// ---------------------------------------------------------------------------
// Constants (must match flat_backward_continuation.cuh)
// ---------------------------------------------------------------------------

// ===========================================================================
// Round 1 static description (mixed base_after_one + continuing sources)
// ===========================================================================

use super::GpuBaseFieldSourceKind;

/// Base-after-one source entry — mirrors `gkr_base_after_one_source<bf, e4>` layout.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatBaseAfterOneSourceEntry {
    pub(super) base_layer_half_size: usize,
    pub(super) next_layer_size: usize,
    pub(super) base_input_start: *const u8,     // *const bf
    pub(super) this_layer_cache_start: *mut u8, // *mut E4
    pub(super) first_access: bool,
    pub(super) source_kind: GpuBaseFieldSourceKind,
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
pub(super) struct Round1FusedSources {
    pub(super) base_sources: Box<[GpuFlatBaseAfterOneSourceEntry; FLAT_CONT_MAX_BASE_SOURCES]>,
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES]>,
    pub(super) num_ext_sources: u32,
    pub(super) idx_remap: Vec<u16>,
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
pub(super) struct GpuFlatBaseAfterTwoSourceEntry {
    pub(super) base_input_start: *const u8,     // *const bf
    pub(super) this_layer_cache_start: *mut u8, // *mut E4
    pub(super) base_layer_half_size: usize,
    pub(super) base_quarter_size: usize,
    pub(super) next_layer_size: usize,
    pub(super) first_access: bool,
    pub(super) source_kind: GpuBaseFieldSourceKind,
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
pub(super) struct Round2FusedSources {
    pub(super) base_sources: Box<[GpuFlatBaseAfterTwoSourceEntry; FLAT_CONT_MAX_BASE_SOURCES]>,
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES]>,
    pub(super) num_ext_sources: u32,
    pub(super) idx_remap: Vec<u16>,
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

#[cfg(test)]
mod tests;

// ===========================================================================
// Diagnostic dump for round 1 flat plan
// ===========================================================================

/// Format a source index for display: "B3" for base, "E7" for ext.
fn fmt_source(idx: u16, assignments: &[ContinuationSourceAssignment]) -> String {
    let a = assignments
        .iter()
        .find(|a| a.source_table_idx == idx as u32);
    match a {
        Some(a) if a.is_ext => format!("E{}", idx),
        Some(_) => format!("B{}", idx),
        None => format!("?{}", idx),
    }
}

/// Format a coefficient recipe as a short string.
fn fmt_recipe<E: std::fmt::Debug>(recipe: &CoefficientRecipe<E>) -> String {
    let mut s = format!("β^{}", recipe.batch_power);
    if recipe.negate {
        s.push_str(" NEG");
    }
    if !recipe.prefactors.is_empty() {
        s.push_str(&format!(" ×{}pf", recipe.prefactors.len()));
    }
    s
}

/// Dump a human-readable representation of the round 1 flat plan.
/// Called from `prepare_layer_from_blueprints` when `GPU_PROVER_DUMP_FLAT_PLAN` is set.
pub(super) fn dump_flat_round1_plan<E: Field + field::FieldExtension<BF> + std::fmt::Debug>(
    layer_idx: usize,
    round1_desc: Option<&Round1FusedSources>,
    continuation_plan: Option<&FlatContinuationBuildPlan<E>>,
    kernel_plans: &[super::backward_kernels::GpuGKRMainLayerKernelPlan<E>],
) {
    let Some(plan) = continuation_plan else {
        eprintln!(
            "=== FLAT ROUND 1 PLAN: layer {} — no continuation plan ===",
            layer_idx
        );
        return;
    };
    let Some(desc) = round1_desc else {
        eprintln!(
            "=== FLAT ROUND 1 PLAN: layer {} — no round 1 desc ===",
            layer_idx
        );
        return;
    };

    let td = &plan.term_desc;
    let assignments = &plan.source_assignments;
    let recipes = &plan.recipes;

    eprintln!("=== FLAT ROUND 1 PLAN: layer {} ===", layer_idx);
    eprintln!(
        "  sources: {} total ({} base, {} ext in round1 desc)",
        td.num_sources, desc.num_base_sources, desc.num_ext_sources
    );
    eprintln!(
        "  terms: {} constants, {} c0_only_linear, {} unified_quadratic, {} unified_linear",
        td.num_constants, td.num_c0_only_linear, td.num_unified_quadratic, td.num_unified_linear
    );
    eprintln!("  coefficients: {}", recipes.len());
    eprintln!();

    // --- Source table ---
    // Build a map: continuation source_table_idx → (gate_idx, is_ext, input_idx)
    // and determine first_access from round1 desc.
    // The round1 desc has separate base/ext arrays; we need the remap.
    // Reconstruct it: iterate assignments in order, track base/ext count.
    let mut base_count = 0u32;
    let mut ext_count = 0u32;
    // Map continuation source_table_idx → (round1 base_idx or ext_idx, is_ext)
    let mut src_remap: std::collections::HashMap<u32, (u32, bool)> =
        std::collections::HashMap::new();
    for a in assignments {
        if !src_remap.contains_key(&a.source_table_idx) {
            if a.is_ext {
                src_remap.insert(a.source_table_idx, (ext_count, true));
                ext_count += 1;
            } else {
                src_remap.insert(a.source_table_idx, (base_count, false));
                base_count += 1;
            }
        }
    }

    eprintln!("--- SOURCES ---");
    // Print by continuation source_table_idx order
    let mut src_indices: Vec<u32> = src_remap.keys().copied().collect();
    src_indices.sort();
    for &sidx in &src_indices {
        let (round1_idx, is_ext) = src_remap[&sidx];
        let a = assignments
            .iter()
            .find(|a| a.source_table_idx == sidx)
            .unwrap();
        let gate_kind = kernel_plans[a.gate_idx].kind;
        let first_access = if is_ext {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_ext_sources as usize {
                !desc.ext_sources[r1idx].previous_layer_start.is_null()
            } else {
                false
            }
        } else {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_base_sources as usize {
                desc.base_sources[r1idx].first_access
            } else {
                false
            }
        };
        let tag = if is_ext { "E" } else { "B" };
        let fa = if first_access { " FIRST_ACCESS" } else { "" };
        let kind_info = if !is_ext {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_base_sources as usize {
                format!(" kind={:?}", desc.base_sources[r1idx].source_kind)
            } else {
                String::new()
            }
        } else {
            String::new()
        };
        eprintln!(
            "  [{tag}{sidx}] gate={gate_kind:?}(#{gate}) input={input}{kind_info}{fa}",
            gate = a.gate_idx,
            input = a.input_idx,
        );
    }
    eprintln!();

    // --- Terms by category ---
    // Recipes are ordered: constants, c0_only_linear, unified_quadratic, unified_linear
    let mut recipe_idx = 0usize;

    eprintln!("--- CONSTANTS ({}) ---", td.num_constants);
    for i in 0..td.num_constants as usize {
        let r = &recipes[recipe_idx];
        eprintln!("  [{i}] {}", fmt_recipe(r));
        recipe_idx += 1;
    }
    if td.num_constants > 0 {
        eprintln!();
    }

    eprintln!("--- C0_ONLY_LINEAR ({}) ---", td.num_c0_only_linear);
    for i in 0..td.num_c0_only_linear as usize {
        let src = td.c0_only_linear[i].source_idx;
        let r = &recipes[recipe_idx];
        eprintln!(
            "  [{i}] src={} {}",
            fmt_source(src, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_c0_only_linear > 0 {
        eprintln!();
    }

    eprintln!("--- UNIFIED_QUADRATIC ({}) ---", td.num_unified_quadratic);
    for i in 0..td.num_unified_quadratic as usize {
        let t = td.unified_quadratic[i];
        let r = &recipes[recipe_idx];
        eprintln!(
            "  [{i}] src_a={} src_b={} {}",
            fmt_source(t.source_a, assignments),
            fmt_source(t.source_b, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_unified_quadratic > 0 {
        eprintln!();
    }

    eprintln!("--- UNIFIED_LINEAR ({}) ---", td.num_unified_linear);
    for i in 0..td.num_unified_linear as usize {
        let src = td.unified_linear[i].source_idx;
        let r = &recipes[recipe_idx];
        eprintln!(
            "  [{i}] src={} {}",
            fmt_source(src, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_unified_linear > 0 {
        eprintln!();
    }

    // --- Source reuse summary ---
    eprintln!("--- SOURCE REUSE ---");
    let mut reuse: std::collections::HashMap<u16, Vec<String>> = std::collections::HashMap::new();

    for i in 0..td.num_c0_only_linear as usize {
        reuse
            .entry(td.c0_only_linear[i].source_idx)
            .or_default()
            .push(format!("c0_lin[{i}]"));
    }
    for i in 0..td.num_unified_quadratic as usize {
        let t = td.unified_quadratic[i];
        reuse
            .entry(t.source_a)
            .or_default()
            .push(format!("quad[{i}].a"));
        reuse
            .entry(t.source_b)
            .or_default()
            .push(format!("quad[{i}].b"));
    }
    for i in 0..td.num_unified_linear as usize {
        reuse
            .entry(td.unified_linear[i].source_idx)
            .or_default()
            .push(format!("u_lin[{i}]"));
    }

    let mut reuse_entries: Vec<_> = reuse.into_iter().collect();
    reuse_entries.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
    for (sidx, refs) in &reuse_entries {
        let (round1_idx, is_ext) = src_remap
            .get(&(*sidx as u32))
            .copied()
            .unwrap_or((0, false));
        let first_access = if is_ext {
            let r1idx = round1_idx as usize;
            r1idx < desc.num_ext_sources as usize
                && !desc.ext_sources[r1idx].previous_layer_start.is_null()
        } else {
            let r1idx = round1_idx as usize;
            r1idx < desc.num_base_sources as usize && desc.base_sources[r1idx].first_access
        };
        let fa = if first_access { " FIRST_ACCESS" } else { "" };
        eprintln!(
            "  {} → {} refs: {}{fa}",
            fmt_source(*sidx, assignments),
            refs.len(),
            refs.join(", "),
        );
    }
    eprintln!("=== END FLAT ROUND 1 PLAN: layer {} ===", layer_idx);
    eprintln!();
}
