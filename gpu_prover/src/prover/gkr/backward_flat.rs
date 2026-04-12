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
use field::Field;

use crate::primitives::context::ProverContext;
use crate::primitives::field::E4;

use super::backward_kernels::{
    gkr_dim_reducing_launch_config, GpuGKRMainLayerConstraintMetadataSource,
    GpuGKRMainLayerConstraintTemplate, GpuGKRMainLayerKernelKind,
};
use super::{
    GpuBaseFieldPolySource, GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0LaunchDescriptors,
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

/// Static structural description for the flat round 0 kernel.
/// Sources are encoded as raw pointers: real device pointers for memory-backed
/// sources, low-bit-tagged null pointers for virtual sources (kind in bits 0..2).
/// Coefficients live in a separate device allocation (challenge-dependent).
/// Passed as `__grid_constant__`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatRound0StaticDesc {
    pub(super) sources: [*const u8; FLAT_ROUND0_MAX_SOURCES],
    pub(super) num_sources: u32,

    pub(super) c0_bf: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_BF],
    pub(super) num_c0_bf: u32,
    pub(super) c0_ext: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C0_EXT],
    pub(super) num_c0_ext: u32,

    pub(super) c1_bf_bf: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_BF],
    pub(super) num_c1_bf_bf: u32,
    pub(super) c1_e4_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_E4_E4],
    pub(super) num_c1_e4_e4: u32,
    pub(super) c1_bf_e4: [GpuFlatC1Pair; FLAT_ROUND0_MAX_C1_BF_E4],
    pub(super) num_c1_bf_e4: u32,

    pub(super) c1_linear: [GpuFlatC0Ref; FLAT_ROUND0_MAX_C1_LINEAR],
    pub(super) num_c1_linear: u32,
}

unsafe impl Send for GpuFlatRound0StaticDesc {}
unsafe impl Sync for GpuFlatRound0StaticDesc {}

impl Default for GpuFlatRound0StaticDesc {
    fn default() -> Self {
        Self {
            sources: [std::ptr::null(); FLAT_ROUND0_MAX_SOURCES],
            num_sources: 0,
            c0_bf: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C0_BF],
            num_c0_bf: 0,
            c0_ext: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C0_EXT],
            num_c0_ext: 0,
            c1_bf_bf: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_BF_BF],
            num_c1_bf_bf: 0,
            c1_e4_e4: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_E4_E4],
            num_c1_e4_e4: 0,
            c1_bf_e4: [GpuFlatC1Pair::default(); FLAT_ROUND0_MAX_C1_BF_E4],
            num_c1_bf_e4: 0,
            c1_linear: [GpuFlatC0Ref::default(); FLAT_ROUND0_MAX_C1_LINEAR],
            num_c1_linear: 0,
        }
    }
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
    pub(super) immediate_factor: E,
    /// 0..2 additional challenge prefactors evaluated at runtime.
    pub(super) prefactors: Vec<Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
}

/// Resolve a single coefficient recipe given runtime challenge values.
pub(super) fn resolve_coefficient<E: Field + field::FieldExtension<BF>>(
    recipe: &CoefficientRecipe<E>,
    batch_challenge_base: E,
    lookup_multiplicative: E,
    lookup_additive: E,
    constraint_batch: E,
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
            constraint_batch,
        );
        coeff.mul_assign(&pf);
    }
    coeff
}

// ---------------------------------------------------------------------------
// Build plan: static desc + recipes, produced at prepare time
// ---------------------------------------------------------------------------

/// Complete build plan for the flat round 0 kernel.
/// Built at prepare time; recipes resolved at schedule time.
pub(super) struct FlatRound0BuildPlan<E> {
    pub(super) static_desc: Box<GpuFlatRound0StaticDesc>,
    pub(super) recipes: Vec<CoefficientRecipe<E>>,
}

impl<E: Field + field::FieldExtension<BF>> FlatRound0BuildPlan<E> {
    pub(super) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }

    /// Resolve all recipes into concrete coefficients.
    pub(super) fn resolve_all(
        &self,
        batch_challenge_base: E,
        lookup_multiplicative: E,
        lookup_additive: E,
        constraint_batch: E,
    ) -> Vec<E> {
        self.recipes
            .iter()
            .map(|r| {
                resolve_coefficient(
                    r,
                    batch_challenge_base,
                    lookup_multiplicative,
                    lookup_additive,
                    constraint_batch,
                )
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Kernel declaration and launch
// ---------------------------------------------------------------------------

use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

/// One-time setup: minimize shared memory carveout to maximize L1 capacity
/// for all flat round 0 kernel variants. Called once before first use.
pub(in crate::prover) fn configure_flat_kernel_cache_preference() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        for kernel in [
            ab_gkr_main_round0_flat_e4_kernel as *const std::ffi::c_void,
            ab_gkr_main_round0_flat_constant_e4_kernel as *const std::ffi::c_void,
        ] {
            let err = unsafe {
                cudaFuncSetAttribute(
                    kernel,
                    CudaFuncAttribute::PreferredSharedMemoryCarveout,
                    0, // 0% shared memory → maximize L1
                )
            };
            if err != era_cudart_sys::CudaError::Success {
                log::warn!(
                    "cudaFuncSetAttribute(PreferredSharedMemoryCarveout, 0) returned {:?}",
                    err
                );
            }
        }
    });
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound0Flat<T>,
    static_desc: GpuFlatRound0StaticDesc,
    coefficients: *const T,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round0_flat_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        coefficients: *const E4,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(super) trait GpuFlatRound0KernelSet: Field {
    const MAIN_ROUND0_FLAT: GpuGKRMainRound0FlatSignature<Self>;
}

impl GpuFlatRound0KernelSet for E4 {
    const MAIN_ROUND0_FLAT: GpuGKRMainRound0FlatSignature<Self> = ab_gkr_main_round0_flat_e4_kernel;
}

pub(super) fn launch_main_round0_flat<E: GpuFlatRound0KernelSet>(
    static_desc: &GpuFlatRound0StaticDesc,
    coefficients: *const E,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatArguments::new(
        *static_desc,
        coefficients,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatFunction(E::MAIN_ROUND0_FLAT).launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Constant-path kernel (reads coefficients from __constant__ symbol)
// ---------------------------------------------------------------------------

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound0FlatConstant<T>,
    static_desc: GpuFlatRound0StaticDesc,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round0_flat_constant_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(super) trait GpuFlatRound0ConstantKernelSet: Field {
    const MAIN_ROUND0_FLAT_CONSTANT: GpuGKRMainRound0FlatConstantSignature<Self>;
}

impl GpuFlatRound0ConstantKernelSet for E4 {
    const MAIN_ROUND0_FLAT_CONSTANT: GpuGKRMainRound0FlatConstantSignature<Self> =
        ab_gkr_main_round0_flat_constant_e4_kernel;
}

pub(super) fn launch_main_round0_flat_constant<E: GpuFlatRound0ConstantKernelSet>(
    static_desc: &GpuFlatRound0StaticDesc,
    eq_values: *const E,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatConstantArguments::new(
        *static_desc,
        eq_values,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatConstantFunction(E::MAIN_ROUND0_FLAT_CONSTANT).launch(&config, &args)
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
use crate::ops::eval_recipes::{GpuPrefactorTerm, GpuRecipeHeader};

/// Compiled recipe buffer ready for device upload.
pub(super) struct CompiledRecipeBuffers {
    pub(super) headers: Vec<GpuRecipeHeader>,
    pub(super) terms: Vec<GpuPrefactorTerm>,
}

/// Compile `CoefficientRecipe` entries into the device-side format.
pub(super) fn compile_recipes_for_device<E: Field + field::FieldExtension<BF>>(
    recipes: &[CoefficientRecipe<E>],
) -> CompiledRecipeBuffers {
    let mut headers = Vec::with_capacity(recipes.len());
    let mut terms = Vec::new();

    for recipe in recipes {
        let mut immediate = recipe.immediate_factor;
        if recipe.negate {
            Field::negate(&mut immediate);
        }

        let terms_offset = terms.len() as u32;
        let mut group_counts = [0u16; 2];

        for (g, group) in recipe.prefactors.iter().enumerate() {
            assert!(g < 2, "at most 2 prefactor groups per recipe");
            group_counts[g] = group.len() as u16;
            for term in group {
                let source = match term.source {
                    GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => 0u32,
                    GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => 1u32,
                    GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch => 2u32,
                };
                terms.push(GpuPrefactorTerm {
                    coeff: term.coeff,
                    source,
                    power: term.power,
                });
            }
        }

        // Cast E → E4 for the device struct.
        // SAFETY: E is always E4 in practice (the only impl of GpuFlatRound0KernelSet).
        let immediate_e4: E4 = unsafe { std::mem::transmute_copy(&immediate) };

        headers.push(GpuRecipeHeader {
            batch_power: recipe.batch_power,
            immediate_factor: immediate_e4,
            num_groups: recipe.prefactors.len() as u16,
            group_counts,
            terms_offset,
        });
    }

    CompiledRecipeBuffers { headers, terms }
}

// ---------------------------------------------------------------------------
// Source table builder
// ---------------------------------------------------------------------------

/// Source deduplication key — just the encoded pointer value.
/// Virtual sources get different "pointer" values (low-bit tags on null),
/// so they naturally deduplicate correctly.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum SourceKey {
    Ptr(usize),
}

pub(super) struct FlatDescriptionBuilder<E> {
    desc: Box<GpuFlatRound0StaticDesc>,
    // Per-tier recipe Vecs — concatenated in tier order in finish().
    recipes_c0_bf: Vec<CoefficientRecipe<E>>,
    recipes_c0_ext: Vec<CoefficientRecipe<E>>,
    recipes_c1_bf_bf: Vec<CoefficientRecipe<E>>,
    recipes_c1_e4_e4: Vec<CoefficientRecipe<E>>,
    recipes_c1_bf_e4: Vec<CoefficientRecipe<E>>,
    recipes_c1_linear: Vec<CoefficientRecipe<E>>,
    source_map: HashMap<SourceKey, u32>,
}

impl<E: Field> FlatDescriptionBuilder<E> {
    pub(super) fn new() -> Self {
        Self {
            desc: Box::new(GpuFlatRound0StaticDesc::default()),
            recipes_c0_bf: Vec::new(),
            recipes_c0_ext: Vec::new(),
            recipes_c1_bf_bf: Vec::new(),
            recipes_c1_e4_e4: Vec::new(),
            recipes_c1_bf_e4: Vec::new(),
            recipes_c1_linear: Vec::new(),
            source_map: HashMap::new(),
        }
    }

    pub(super) fn add_bf_source<B>(&mut self, src: &GpuBaseFieldPolySource<B>) -> u32 {
        // Encode virtual sources as low-bit-tagged null pointers.
        let encoded_ptr = if src.source_kind as u32 >= 2 {
            // Virtual source: encode kind in low bits of null pointer
            src.source_kind as u32 as usize as *const u8
        } else {
            src.start as *const u8
        };
        let key = SourceKey::Ptr(encoded_ptr as usize);
        if let Some(&idx) = self.source_map.get(&key) {
            return idx;
        }
        let idx = self.desc.num_sources;
        assert!(
            (idx as usize) < FLAT_ROUND0_MAX_SOURCES,
            "flat round0: source table overflow ({idx} >= {FLAT_ROUND0_MAX_SOURCES})",
        );
        self.desc.sources[idx as usize] = encoded_ptr;
        self.desc.num_sources = idx + 1;
        self.source_map.insert(key, idx);
        idx
    }

    pub(super) fn add_ext_source(&mut self, src: &GpuExtensionFieldPolyInitialSource<E>) -> u32 {
        let key = SourceKey::Ptr(src.start as usize);
        if let Some(&idx) = self.source_map.get(&key) {
            return idx;
        }
        let idx = self.desc.num_sources;
        assert!(
            (idx as usize) < FLAT_ROUND0_MAX_SOURCES,
            "flat round0: source table overflow ({idx} >= {FLAT_ROUND0_MAX_SOURCES})",
        );
        self.desc.sources[idx as usize] = src.start as *const u8;
        self.desc.num_sources = idx + 1;
        self.source_map.insert(key, idx);
        idx
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

    pub(super) fn finish(self) -> FlatRound0BuildPlan<E> {
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

/// Build the flat plan from prepared gates.
pub(super) fn build_flat_round0_plan<E: Field>(
    gates: &[PreparedGateForFlatPlan<'_, E>],
) -> FlatRound0BuildPlan<E> {
    let mut b = FlatDescriptionBuilder::<E>::new();

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
                prefactors: vec![],
            }
        };
        let bc1 = || -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p1,
                negate: false,
                immediate_factor: E::ONE,
                prefactors: vec![],
            }
        };
        let neg_bc0 = || -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: true,
                immediate_factor: E::ONE,
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
    b: &mut FlatDescriptionBuilder<E>,
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
    b: &mut FlatDescriptionBuilder<E>,
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
                    b.push_c1_bf_bf(
                        lhs,
                        rhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
    b: &mut FlatDescriptionBuilder<E>,
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
    b: &mut FlatDescriptionBuilder<E>,
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
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c1_bf_bf(
                        cached_src,
                        form_src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c1_bf_bf(
                        cached_src,
                        form_src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
    b: &mut FlatDescriptionBuilder<E>,
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
                prefactors: vec![lt.challenge_terms.clone()],
            },
        );
    }
}

fn emit_single_times_linear_form_deferred_quad<E: Field>(
    b: &mut FlatDescriptionBuilder<E>,
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
                prefactors: vec![qt.challenge_terms.clone()],
            },
        );
    }
}

/// Emit terms: β * Σ(linear_form_terms_j · Δⱼ_bf) * Δ(ext_src)
fn emit_linear_form_times_ext<E: Field>(
    b: &mut FlatDescriptionBuilder<E>,
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
                if negate {
                    Field::negate(&mut coeff);
                }
                b.push_c1_bf_e4(
                    bf_src,
                    ext_src,
                    CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: coeff,
                        prefactors: vec![],
                    },
                );
            }
        }
        None => panic!("gate requires metadata"),
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

    use super::super::backward_kernels::GpuGKRMainLayerKernelKind;
    use super::super::GpuBaseFieldSourceKind;

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

    /// Test the flat kernel with a BaseCopy gate using a Resolved recipe.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round0_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let output_values: Vec<BF> = (0..4).map(|i| BF::new(100 + i)).collect();
        let batch_challenge = sample_ext(200);
        let claim_challenge = sample_ext(60);

        let output_dev = alloc_and_copy(&context, &output_values);
        let eq = {
            let mut one_minus = E4::ONE;
            one_minus.sub_assign(&claim_challenge);
            [one_minus, claim_challenge]
        };
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        // Build plan with a Resolved recipe (test path)
        let mut b = FlatDescriptionBuilder::new();
        let out = b.add_bf_source(&GpuBaseFieldPolySource {
            start: output_dev.as_ptr(),
            next_layer_size: acc_size,
            source_kind: GpuBaseFieldSourceKind::Real,
        });
        b.push_c0_bf(
            out,
            CoefficientRecipe {
                batch_power: 0,
                negate: false,
                immediate_factor: batch_challenge,
                prefactors: vec![],
            },
        );
        let plan = b.finish();

        let coeffs = plan.resolve_all(E4::ONE, E4::ZERO, E4::ZERO, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        launch_main_round0_flat(
            &plan.static_desc,
            coeffs_dev.as_ptr(),
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);

        // CPU reference: c0 = batch_challenge * output[gid] * eq[gid], c1 = 0
        let mut expected = Vec::new();
        for gid in 0..acc_size {
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[gid]);
            c0.mul_assign(&eq[gid]);
            expected.push(c0);
        }
        for _ in 0..acc_size {
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, expected, "flat round0 BaseCopy mismatch");
    }

    /// Test the flat kernel with a Product gate using Deferred recipes + resolve.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round0_product_deferred_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;

        let input0: Vec<E4> = (0..4).map(|i| sample_ext(10 + i * 10)).collect();
        let input1: Vec<E4> = (0..4).map(|i| sample_ext(50 + i * 10)).collect();
        let output: Vec<E4> = (0..4).map(|i| sample_ext(90 + i * 10)).collect();

        let input0_dev = alloc_and_copy(&context, &input0);
        let input1_dev = alloc_and_copy(&context, &input1);
        let output_dev = alloc_and_copy(&context, &output);

        let batch_challenge_base = sample_ext(300);
        let claim_challenge = sample_ext(200);

        let eq = {
            let mut one_minus = E4::ONE;
            one_minus.sub_assign(&claim_challenge);
            [one_minus, claim_challenge]
        };
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        // Build plan using build_flat_round0_plan (Deferred recipes)
        let r0_desc = GpuSumcheckRound0LaunchDescriptors {
            base_field_inputs: vec![],
            extension_field_inputs: vec![
                GpuExtensionFieldPolyInitialSource {
                    start: input0_dev.as_ptr(),
                    next_layer_size: acc_size,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: input1_dev.as_ptr(),
                    next_layer_size: acc_size,
                },
            ],
            base_field_outputs: vec![],
            extension_field_outputs: vec![GpuExtensionFieldPolyInitialSource {
                start: output_dev.as_ptr(),
                next_layer_size: acc_size,
            }],
        };
        let gate = PreparedGateForFlatPlan {
            kind: GpuGKRMainLayerKernelKind::Product,
            round0: &r0_desc,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        };
        let plan = build_flat_round0_plan(&[gate]);

        // Resolve: batch_power=0 → base^0 = 1
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, E4::ZERO, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        launch_main_round0_flat(
            &plan.static_desc,
            coeffs_dev.as_ptr(),
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);

        // CPU: batch_challenge = base.pow(0) = ONE
        let bc = E4::ONE;
        let mut expected = Vec::new();
        for gid in 0..acc_size {
            let mut c0 = bc;
            c0.mul_assign(&output[gid]);
            c0.mul_assign(&eq[gid]);
            expected.push(c0);
        }
        for gid in 0..acc_size {
            let mut delta_a = input0[gid + acc_size];
            delta_a.sub_assign(&input0[gid]);
            let mut delta_b = input1[gid + acc_size];
            delta_b.sub_assign(&input1[gid]);
            let mut c1 = bc;
            c1.mul_assign(&delta_a);
            c1.mul_assign(&delta_b);
            c1.mul_assign(&eq[gid]);
            expected.push(c1);
        }

        assert_eq!(actual, expected, "flat round0 Product deferred mismatch");
    }
}
