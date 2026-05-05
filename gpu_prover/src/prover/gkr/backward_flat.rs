//! Flattened GKR backward pass round 0 kernel.
//!
//! Instead of a 20-way switch on gate kind, this compiles every gate in the
//! layer into flat arrays of linear/quadratic terms. The structural part
//! (source table + term pairs) is passed as `__grid_constant__`, while the
//! challenge-dependent coefficients live in a separate device buffer filled
//! at schedule time via a stream callback.

use std::collections::HashMap;

use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, PrimeField};

use crate::ops::immediate_factors::{ImmediateFactorInterner, ImmediateFactorRecipeStructural};
use crate::primitives::context::ProverContext;
use crate::primitives::field::E4;

use super::backward_flat_compact::{
    build_backing_ranges, pack_flat_round0_source_real, pack_flat_round0_source_virtual,
    resolve_backing_for_pointer, BackingRange, FlatRound0BuildPlanCompact,
    GpuFlatRound0StaticDescCompact,
};
use super::backward_kernels::{
    gkr_dim_reducing_launch_config, GpuGKRMainLayerConstraintMetadataSource,
    GpuGKRMainLayerConstraintTemplate, GpuGKRMainLayerKernelKind, GKR_DIM_REDUCING_BASE_SLOTS,
};
use super::{
    GpuBaseFieldPolySource, GpuExtensionFieldPolyInitialSource, GpuGKRStorage,
    GpuSumcheckRound0LaunchDescriptors,
};
use crate::primitives::field::BF;

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
#[derive(Clone)]
pub(super) struct CoefficientRecipe<E> {
    pub(super) batch_power: u32,
    pub(super) negate: bool,
    /// Product factor known at build time (default: E::ONE).
    ///
    /// TODO(perf): for many gates this carries a cs-side `u32` coefficient
    /// promoted via `E::from_base(BF::from_u32_with_reduction(coeff))` (see
    /// `build_single_max_quadratic_constraint_inputs_and_metadata` and the
    /// other `*_inputs_and_metadata` helpers in `backward.rs`). Storing the
    /// value as `E` forces every `c1_bf_bf` evaluation in round 0 (and the
    /// continuation equivalents) to do `E * BF * BF` (~4 base muls on Ext4)
    /// per row when the structurally correct shape is `BF * BF * BF` (~1
    /// base mul) accumulated in BF and lifted to E once per gate via the
    /// gate's `batch_power = α^k` factor. Three structural fixes are viable
    /// (none change c1_bf_bf row counts):
    ///   1. `immediate_factor: ImmediateFactor::Base(BF) | Ext(E)` sum-type
    ///      with a parallel BF table the kernel reads when the BF variant is
    ///      selected.
    ///   2. Partition c1_bf_bf into `c1_bf_bf_bf` (pure-BF coefficient) +
    ///      existing `c1_bf_bf` (mixed/E coefficient). New term type, but
    ///      each BF row's coefficient shrinks from 16 B to 4 B — descriptor-
    ///      bytes win on top of the compute win.
    ///   3. Defer the BF→E lift entirely: keep `immediate_factor: BF` and let
    ///      the kernel pick the right multiplication width based on a single
    ///      discriminator bit; the result genuinely lives in E only after the
    ///      `batch_power` multiplication.
    /// Out of scope for Phase D ceiling tightening (this is a per-row cost
    /// optimization, not a row-count change). Deferred-form templates that
    /// carry real verifier challenges via `prefactors` must remain E.
    pub(super) immediate_factor: E,
    pub(super) immediate_recipe: ImmediateFactorRecipeStructural,
    /// 0..2 additional challenge prefactors evaluated at runtime.
    pub(super) prefactors: Vec<Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
}

/// Resolve a single coefficient recipe given runtime challenge values.
pub(super) fn resolve_coefficient<E: Field + field::FieldExtension<BF>>(
    recipe: &CoefficientRecipe<E>,
    batch_challenge_base: E,
    lookup_multiplicative: E,
    lookup_additive: E,
) -> E {
    let mut coeff = batch_challenge_base.pow(recipe.batch_power);
    coeff.mul_assign(&recipe.immediate_factor);
    if recipe.negate {
        Field::negate(&mut coeff);
    }
    for terms in &recipe.prefactors {
        let pf = super::backward::evaluate_constraint_prefactor(
            terms,
            lookup_multiplicative,
            lookup_additive,
        );
        coeff.mul_assign(&pf);
    }
    coeff
}

fn immediate_recipe_with_negation(
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

    /// Resolve all recipes into concrete coefficients.
    pub(super) fn resolve_all(
        &self,
        batch_challenge_base: E,
        lookup_multiplicative: E,
        lookup_additive: E,
    ) -> Vec<E> {
        self.recipes
            .iter()
            .map(|r| {
                resolve_coefficient(
                    r,
                    batch_challenge_base,
                    lookup_multiplicative,
                    lookup_additive,
                )
            })
            .collect()
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
use crate::ops::eval_recipes::{
    GpuFlatRecipeEvalDesc, GpuPrefactorTerm, GpuRecipeHeader, FLAT_IMMEDIATE_MAX_MONOMIALS,
    FLAT_IMMEDIATE_MAX_RECIPES, FLAT_RECIPE_MAX_HEADERS, FLAT_RECIPE_MAX_TERMS,
};

/// Compiled recipe buffer ready for device upload.
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
    /// exceeded (Phase 0 confirms ≤ 5 distinct classes per launch).
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

const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;

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

pub(super) const FLAT_CONT_CONST_MAX: usize = 1024;
pub(super) const FLAT_CONT_MAX_SOURCES: usize = 512;
pub(super) const FLAT_CONT_MAX_C0_ONLY_LINEAR: usize = 640;
pub(super) const FLAT_CONT_MAX_UNIFIED_QUADRATIC: usize = 4608;
pub(super) const FLAT_CONT_MAX_UNIFIED_LINEAR: usize = 128;
pub(super) const FLAT_CONT_MAX_CONSTANT: usize = 64;

// Round 1/2 mixed source limits
pub(super) const FLAT_CONT_MAX_BASE_SOURCES: usize = 128;
pub(super) const FLAT_CONT_MAX_EXT_SOURCES: usize = 384;
pub(super) const FLAT_CONT_EXT_SOURCE_BIT: u16 = 0x8000;

// Unified tiled kernel constants
pub(super) const FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE: usize = 4;
pub(super) const FLAT_CONT_UNIFIED_MAX_GRID_DIM: usize =
    (FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES) / FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE;
pub(super) const FLAT_CONT_UNIFIED_MAX_TERMS: usize = 1024;
// Sparse: only non-empty tiles stored. Each tile has ≥1 term, so max tiles ≤ max terms.
pub(super) const FLAT_CONT_UNIFIED_MAX_TILES: usize = FLAT_CONT_UNIFIED_MAX_TERMS;
pub(super) const FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES: usize =
    FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES;

// ---------------------------------------------------------------------------
// Static description types (mirror CUDA structs)
// ---------------------------------------------------------------------------

/// Compact source descriptor for continuing sources.
/// `previous_layer_start == null` encodes `!first_access` (read from cache).
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatContinuingSourceEntry {
    pub(super) previous_layer_start: *const u8,
    pub(super) this_layer_cache_start: *mut u8,
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
/// steps. The sources array used to live here too (alongside `num_sources`)
/// in the legacy `GpuFlatContinuationStaticDesc`, but per-step source data
/// is now passed separately to the compact builder, so the term-only form
/// is enough for `FlatContinuationBuildPlan`.
#[derive(Clone)]
pub(super) struct FlatContinuationTermDesc {
    pub(super) num_sources: u32,

    pub(super) c0_only_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR]>,
    pub(super) num_c0_only_linear: u32,

    pub(super) unified_quadratic: Box<[GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC]>,
    pub(super) num_unified_quadratic: u32,

    pub(super) unified_linear: Box<[GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR]>,
    pub(super) num_unified_linear: u32,

    pub(super) num_constants: u32,
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
pub(super) struct FlatContinuationBuildPlan<E> {
    pub(super) term_desc: FlatContinuationTermDesc,
    pub(super) recipes: Vec<CoefficientRecipe<E>>,
    /// One entry per unique source: records the first (gate_idx, is_ext, input_idx)
    /// that mapped to a source table index. Used to populate per-step source entries.
    pub(super) source_assignments: Vec<ContinuationSourceAssignment>,
}

/// Records which source table slot a particular gate input maps to.
#[derive(Clone)]
pub(super) struct ContinuationSourceAssignment {
    pub(super) gate_idx: usize,
    pub(super) is_ext: bool,
    pub(super) input_idx: usize,
    pub(super) source_table_idx: u32,
}

impl<E: Field + field::FieldExtension<BF>> FlatContinuationBuildPlan<E> {
    pub(super) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }

    pub(super) fn resolve_all(
        &self,
        batch_challenge_base: E,
        lookup_multiplicative: E,
        lookup_additive: E,
    ) -> Vec<E> {
        self.recipes
            .iter()
            .map(|r| {
                resolve_coefficient(
                    r,
                    batch_challenge_base,
                    lookup_multiplicative,
                    lookup_additive,
                )
            })
            .collect()
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

pub(super) struct FlatContinuationDescriptionBuilder<E> {
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
    pub(super) fn new() -> Self {
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
    pub(super) fn add_source(
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

    pub(super) fn push_constant(&mut self, recipe: CoefficientRecipe<E>) {
        let i = self.desc.num_constants as usize;
        assert!(
            i < FLAT_CONT_MAX_CONSTANT,
            "flat continuation: constant overflow"
        );
        self.desc.num_constants += 1;
        self.recipes_constants.push(recipe);
    }

    pub(super) fn push_c0_only_linear(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
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

    pub(super) fn push_unified_quadratic(
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

    pub(super) fn push_unified_linear(&mut self, source_idx: u32, recipe: CoefficientRecipe<E>) {
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

    pub(super) fn finish(mut self) -> FlatContinuationBuildPlan<E> {
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

use super::GpuExtensionFieldPolyContinuingSourcePlan;

/// Per-gate data needed for building the flat continuation plan.
pub(super) struct PreparedGateForFlatContinuationPlan<'a, E> {
    pub(super) kind: GpuGKRMainLayerKernelKind,
    pub(super) gate_idx: usize,
    /// Base field inputs (as continuing sources in round 3+).
    pub(super) base_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    /// Extension field inputs (as continuing sources).
    pub(super) ext_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    pub(super) batch_challenge_power_offset: u32,
    pub(super) constraint_source: Option<&'a GpuGKRMainLayerConstraintMetadataSource<E>>,
}

/// Build the flat continuation plan from prepared gates.
pub(super) fn build_flat_continuation_plan<E: Field>(
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

pub(super) fn get_constant_continuation_coefficients_device_ptr() -> *mut E4 {
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

pub(super) fn eval_continuation_recipes_e4(
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
/// Replaces the legacy `GpuFlatRound1StaticDesc`: term arrays now live in
/// `plan.term_desc` and the compact builder applies `idx_remap` inline as
/// it constructs compact term records.
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
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::prover::test_utils::make_test_context;
    use era_cudart::memory::memory_copy_async;
    use field::FieldExtension;
    use serial_test::serial;

    use super::super::backward_kernels::{
        GpuGKRMainLayerConstraintChallengeTerm, GpuGKRMainLayerConstraintHostMetadata,
        GpuGKRMainLayerConstraintLinearTemplate, GpuGKRMainLayerConstraintLinearTerm,
        GpuGKRMainLayerConstraintMetadataSource, GpuGKRMainLayerConstraintQuadraticTemplate,
        GpuGKRMainLayerConstraintQuadraticTerm, GpuGKRMainLayerConstraintTemplate,
        GpuGKRMainLayerDeferredChallengeSource, GpuGKRMainLayerKernelKind,
    };
    use super::super::{GpuBaseFieldSourceKind, GpuExtensionFieldPolyContinuingSourcePlan};

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        allocation
    }

    fn read_device<T: Copy>(
        context: &ProverContext,
        dev: &DeviceAllocation<T>,
        len: usize,
    ) -> Vec<T> {
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, dev, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { host.get_accessor().get().to_vec() }
    }

    fn resolve_plan_coeffs(
        plan: &FlatContinuationBuildPlan<E4>,
        batch_challenge_base: E4,
        lookup_multiplicative: E4,
        lookup_additive: E4,
    ) -> Vec<E4> {
        plan.recipes
            .iter()
            .map(|r| {
                resolve_coefficient(
                    r,
                    batch_challenge_base,
                    lookup_multiplicative,
                    lookup_additive,
                )
            })
            .collect()
    }

    fn cont_source(cache_ptr: *mut E4) -> GpuExtensionFieldPolyContinuingSourcePlan<E4> {
        GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: std::ptr::null(),
            this_layer_start: cache_ptr,
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: false,
        }
    }

    fn build_round1_desc_from_plan(
        plan: &FlatContinuationBuildPlan<E4>,
        base_sources: &[Vec<GpuFlatBaseAfterOneSourceEntry>],
        ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
    ) -> Round1FusedSources {
        let mut desc = Round1FusedSources::default();
        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                continue;
            }
            if assignment.is_ext {
                let src = &ext_sources[assignment.gate_idx][assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = *src;
                ext_count += 1;
            } else {
                let src = &base_sources[assignment.gate_idx][assignment.input_idx];
                let tagged_idx = base_count as u16;
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = *src;
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;
        desc
    }

    fn build_round2_desc_from_plan(
        plan: &FlatContinuationBuildPlan<E4>,
        base_sources: &[Vec<GpuFlatBaseAfterTwoSourceEntry>],
        ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
    ) -> Round2FusedSources {
        let mut desc = Round2FusedSources::default();
        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                continue;
            }
            if assignment.is_ext {
                let src = &ext_sources[assignment.gate_idx][assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = *src;
                ext_count += 1;
            } else {
                let src = &base_sources[assignment.gate_idx][assignment.input_idx];
                let tagged_idx = base_count as u16;
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = *src;
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;
        desc
    }

    #[test]
    fn flat_round1_source_remap_sanity() {
        let base_cache = [E4::ZERO; 1];
        let ext_cache = [E4::ZERO; 1];
        let base_inputs = [cont_source(base_cache.as_ptr() as *mut E4)];
        let ext_inputs = [cont_source(ext_cache.as_ptr() as *mut E4)];
        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::MaskIdentity,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &ext_inputs,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);
        let base_sources = vec![vec![GpuFlatBaseAfterOneSourceEntry {
            base_layer_half_size: 4,
            next_layer_size: 2,
            base_input_start: std::ptr::null(),
            this_layer_cache_start: base_cache.as_ptr() as *mut u8,
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }]];
        let ext_sources = vec![vec![GpuFlatContinuingSourceEntry {
            previous_layer_start: std::ptr::null(),
            this_layer_cache_start: ext_cache.as_ptr() as *mut u8,
        }]];
        let desc = build_round1_desc_from_plan(&plan, &base_sources, &ext_sources);
        assert_eq!(desc.num_base_sources, 1);
        assert_eq!(desc.num_ext_sources, 1);
        // 2 continuation sources (one base, one ext) map to {0, FLAT_CONT_EXT_SOURCE_BIT}.
        let mut tags: Vec<u16> = desc.idx_remap.clone();
        tags.sort();
        assert_eq!(tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
    }

    #[test]
    fn flat_round2_source_remap_sanity() {
        let base_cache = [E4::ZERO; 1];
        let ext_cache = [E4::ZERO; 1];
        let base_inputs = [cont_source(base_cache.as_ptr() as *mut E4)];
        let ext_inputs = [cont_source(ext_cache.as_ptr() as *mut E4)];
        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::MaskIdentity,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &ext_inputs,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);
        let base_sources = vec![vec![GpuFlatBaseAfterTwoSourceEntry {
            base_input_start: std::ptr::null(),
            this_layer_cache_start: base_cache.as_ptr() as *mut u8,
            base_layer_half_size: 4,
            base_quarter_size: 2,
            next_layer_size: 1,
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }]];
        let ext_sources = vec![vec![GpuFlatContinuingSourceEntry {
            previous_layer_start: std::ptr::null(),
            this_layer_cache_start: ext_cache.as_ptr() as *mut u8,
        }]];
        let desc = build_round2_desc_from_plan(&plan, &base_sources, &ext_sources);
        assert_eq!(desc.num_base_sources, 1);
        assert_eq!(desc.num_ext_sources, 1);
        // 2 continuation sources (one base, one ext) map to {0, FLAT_CONT_EXT_SOURCE_BIT}.
        let mut tags: Vec<u16> = desc.idx_remap.clone();
        tags.sort();
        assert_eq!(tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
    }

    // Legacy GPU unit tests for the round-0 kernel
    // (`flat_round0_base_copy_matches_cpu`,
    // `flat_round0_product_deferred_matches_cpu`) were deleted with the
    // legacy launcher. End-to-end coverage of the same gate kinds runs
    // through the compact-path stagewise/multi-schedule parity tests
    // (`run_basic_unrolled_*`).

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_continuation_remap_tags_sources() {
        let context = make_test_context(64, 8);

        let shared: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let base_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: shared.as_ptr(),
            this_layer_start: shared.as_ptr().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: true,
        }];
        let ext_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: shared.as_ptr(),
            this_layer_start: shared.as_ptr().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: true,
        }];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::MaskIdentity,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &ext_inputs,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);
        assert_eq!(plan.term_desc.num_sources, 2, "remap: base/ext dedup");

        let base_values: Vec<BF> = (0..8).map(|i| BF::new(5 + i)).collect();
        let ext_values: Vec<E4> = (0..8).map(|i| sample_ext(900 + i)).collect();
        let base_input_dev = alloc_and_copy(&context, &base_values);
        let ext_prev_dev = alloc_and_copy(&context, &ext_values);
        let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let round1_desc = build_round1_desc_from_plan(
            &plan,
            &[vec![GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base_input_dev.as_ptr().cast(),
                this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            }]],
            &[vec![GpuFlatContinuingSourceEntry {
                previous_layer_start: ext_prev_dev.as_ptr().cast(),
                this_layer_cache_start: ext_cache.as_ptr().cast_mut().cast(),
            }]],
        );
        assert_eq!(round1_desc.num_base_sources, 1);
        assert_eq!(round1_desc.num_ext_sources, 1);
        let mut round1_tags: Vec<u16> = round1_desc.idx_remap.clone();
        round1_tags.sort();
        assert_eq!(round1_tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);

        let base_values2: Vec<BF> = (0..16).map(|i| BF::new(15 + i)).collect();
        let base_input_dev2 = alloc_and_copy(&context, &base_values2);
        let base_cache2: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let ext_cache2: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let round2_desc = build_round2_desc_from_plan(
            &plan,
            &[vec![GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_dev2.as_ptr().cast(),
                this_layer_cache_start: base_cache2.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            }]],
            &[vec![GpuFlatContinuingSourceEntry {
                previous_layer_start: ext_prev_dev.as_ptr().cast(),
                this_layer_cache_start: ext_cache2.as_ptr().cast_mut().cast(),
            }]],
        );
        assert_eq!(round2_desc.num_base_sources, 1);
        assert_eq!(round2_desc.num_ext_sources, 1);
        let mut round2_tags: Vec<u16> = round2_desc.idx_remap.clone();
        round2_tags.sort();
        assert_eq!(round2_tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
    }
}

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
