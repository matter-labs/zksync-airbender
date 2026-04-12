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

/// Static structural description for the flat continuation kernels (rounds 1+).
/// Passed as `__grid_constant__`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatContinuationStaticDesc {
    pub(super) sources: [GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES],
    pub(super) num_sources: u32,

    pub(super) c0_only_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR],
    pub(super) num_c0_only_linear: u32,

    pub(super) unified_quadratic: [GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC],
    pub(super) num_unified_quadratic: u32,

    pub(super) unified_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR],
    pub(super) num_unified_linear: u32,

    pub(super) num_constants: u32,
}

unsafe impl Send for GpuFlatContinuationStaticDesc {}
unsafe impl Sync for GpuFlatContinuationStaticDesc {}

impl Default for GpuFlatContinuationStaticDesc {
    fn default() -> Self {
        Self {
            sources: [GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_SOURCES],
            num_sources: 0,
            c0_only_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_C0_ONLY_LINEAR],
            num_c0_only_linear: 0,
            unified_quadratic: [GpuFlatC1Pair::default(); FLAT_CONT_MAX_UNIFIED_QUADRATIC],
            num_unified_quadratic: 0,
            unified_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_UNIFIED_LINEAR],
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
    pub(super) term_desc: Box<GpuFlatContinuationStaticDesc>,
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
// Continuation description builder
// ---------------------------------------------------------------------------

/// Key for deduplicating continuation sources.
/// We deduplicate by cache pointer plus source kind (base/ext), since round 1/2
/// require base/ext separation even when the underlying continuation cache is shared.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ContinuationSourceKey {
    cache_ptr: usize,
    is_ext: bool,
}

pub(super) struct FlatContinuationDescriptionBuilder<E> {
    desc: Box<GpuFlatContinuationStaticDesc>,
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
            desc: Box::new(GpuFlatContinuationStaticDesc::default()),
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
        let idx = self.desc.num_sources;
        assert!(
            (idx as usize) < FLAT_CONT_MAX_SOURCES,
            "flat continuation: source table overflow ({idx} >= {FLAT_CONT_MAX_SOURCES})",
        );
        self.desc.num_sources = idx + 1;
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

    pub(super) fn finish(self) -> FlatContinuationBuildPlan<E> {
        // Concatenate recipes in tier order to match kernel's *coeff++ traversal:
        // constants, c0_only_linear, unified_quadratic, unified_linear
        let mut recipes = self.recipes_constants;
        recipes.extend(self.recipes_c0_only);
        recipes.extend(self.recipes_quadratic);
        recipes.extend(self.recipes_linear);
        FlatContinuationBuildPlan {
            term_desc: self.desc,
            recipes,
            source_assignments: self.source_assignments,
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
                prefactors: vec![gamma_term(coeff, power)],
            }
        };
        let bc1_gamma = |coeff: BF, power: u32| -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p1,
                negate: false,
                immediate_factor: E::ONE,
                prefactors: vec![gamma_term(coeff, power)],
            }
        };
        let neg_bc0_gamma = |coeff: BF, power: u32| -> CoefficientRecipe<E> {
            CoefficientRecipe {
                batch_power: p0,
                negate: true,
                immediate_factor: E::ONE,
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
                        prefactors: vec![],
                    });
                }
            }
            if !meta.constant_offset.is_zero() {
                b.push_constant(CoefficientRecipe {
                    batch_power,
                    negate: false,
                    immediate_factor: meta.constant_offset,
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
                    quad_consts.push(qt.challenge);
                } else {
                    quad_terms.push(qt);
                }
            }
            let mut lin_terms = Vec::new();
            let mut lin_consts = Vec::new();
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    lin_consts.push(lt.challenge);
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
                    b.push_unified_quadratic(
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
                for lc in &lin_consts {
                    let mut coeff = qt.challenge;
                    coeff.mul_assign(lc);
                    b.push_c0_only_linear(
                        lhs,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
                for qc in &quad_consts {
                    let mut coeff = lt.challenge;
                    coeff.mul_assign(qc);
                    b.push_c0_only_linear(
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

            for qc in &quad_consts {
                for lc in &lin_consts {
                    let mut coeff = *qc;
                    coeff.mul_assign(lc);
                    b.push_constant(CoefficientRecipe {
                        batch_power,
                        negate: false,
                        immediate_factor: coeff,
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
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate: false,
                                immediate_factor: coeff,
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
                            prefactors: vec![],
                        },
                    );
                }
            } else {
                for qt in &meta.quadratic_terms {
                    if qt.lhs == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                        let mut coeff = qt.challenge;
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_c0_only_linear(
                            cached_src,
                            CoefficientRecipe {
                                batch_power,
                                negate: false,
                                immediate_factor: coeff,
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
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        src,
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
                        let mut coeff = qt.challenge;
                        if negate {
                            Field::negate(&mut coeff);
                        }
                        b.push_constant(CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        src,
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
                        prefactors: vec![lt.challenge_terms.clone()],
                    },
                );
            }
        }
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(ref meta)) => {
            for lt in &meta.linear_terms {
                if lt.input == NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL {
                    let mut coeff = lt.challenge;
                    if negate {
                        Field::negate(&mut coeff);
                    }
                    b.push_c0_only_linear(
                        ext_src,
                        CoefficientRecipe {
                            batch_power,
                            negate: false,
                            immediate_factor: coeff,
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

// Round 3 flat compact: device-ptr coefficients
cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatCompact<T>,
    static_desc: GpuFlatContinuationStaticDesc,
    coefficients: *const T,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round3_flat_compact_e4_kernel(
        static_desc: GpuFlatContinuationStaticDesc,
        coefficients: *const E4,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

// Round 3 flat explicit: device-ptr coefficients
cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatExplicit<T>,
    static_desc: GpuFlatContinuationStaticDesc,
    coefficients: *const T,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round3_flat_explicit_e4_kernel(
        static_desc: GpuFlatContinuationStaticDesc,
        coefficients: *const E4,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

// Round 3 flat constant compact: reads coefficients from __constant__
cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatConstantCompact<T>,
    static_desc: GpuFlatContinuationStaticDesc,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round3_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatContinuationStaticDesc,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

// Round 3 flat constant explicit
cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound3FlatConstantExplicit<T>,
    static_desc: GpuFlatContinuationStaticDesc,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round3_flat_constant_explicit_e4_kernel(
        static_desc: GpuFlatContinuationStaticDesc,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

// Eval recipes kernel for continuation coefficients
cuda_kernel_signature_arguments_and_function!(
    GpuFlatContEvalRecipes<T>,
    challenges: *const T,
    recipes: *const GpuRecipeHeader,
    terms: *const GpuPrefactorTerm,
    coefficients: *mut T,
    num_recipes: u32,
);

cuda_kernel_declaration!(
    ab_gkr_flat_continuation_eval_recipes_e4_kernel(
        challenges: *const E4,
        recipes: *const GpuRecipeHeader,
        terms: *const GpuPrefactorTerm,
        coefficients: *mut E4,
        num_recipes: u32,
    )
);

// ---------------------------------------------------------------------------
// Launch functions
// ---------------------------------------------------------------------------

pub(super) fn launch_main_round3_flat(
    static_desc: &GpuFlatContinuationStaticDesc,
    coefficients: *const E4,
    folding_challenge: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound3FlatExplicitArguments::new(
            *static_desc,
            coefficients,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound3FlatExplicitFunction(ab_gkr_main_round3_flat_explicit_e4_kernel)
            .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound3FlatCompactArguments::new(
            *static_desc,
            coefficients,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound3FlatCompactFunction(ab_gkr_main_round3_flat_compact_e4_kernel)
            .launch(&config, &args)
    }
}

pub(super) fn launch_main_round3_flat_constant(
    static_desc: &GpuFlatContinuationStaticDesc,
    folding_challenge: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound3FlatConstantExplicitArguments::new(
            *static_desc,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound3FlatConstantExplicitFunction(
            ab_gkr_main_round3_flat_constant_explicit_e4_kernel,
        )
        .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound3FlatConstantCompactArguments::new(
            *static_desc,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound3FlatConstantCompactFunction(
            ab_gkr_main_round3_flat_constant_compact_e4_kernel,
        )
        .launch(&config, &args)
    }
}

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
    challenges: *const E4,
    recipes: &era_cudart::slice::DeviceSlice<GpuRecipeHeader>,
    terms: &era_cudart::slice::DeviceSlice<GpuPrefactorTerm>,
    coefficients: *mut E4,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
    use era_cudart::execution::CudaLaunchConfig;

    let num_recipes = recipes.len();
    if num_recipes == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_recipes as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuFlatContEvalRecipesArguments::new(
        challenges,
        recipes.as_ptr(),
        terms.as_ptr(),
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

/// Round 1 static description: mixed base_after_one + continuing sources.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatRound1StaticDesc {
    pub(super) base_sources: [GpuFlatBaseAfterOneSourceEntry; FLAT_CONT_MAX_BASE_SOURCES],
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: [GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES],
    pub(super) num_ext_sources: u32,

    pub(super) c0_only_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR],
    pub(super) num_c0_only_linear: u32,
    pub(super) unified_quadratic: [GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC],
    pub(super) num_unified_quadratic: u32,
    pub(super) unified_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR],
    pub(super) num_unified_linear: u32,
    pub(super) num_constants: u32,
}

unsafe impl Send for GpuFlatRound1StaticDesc {}
unsafe impl Sync for GpuFlatRound1StaticDesc {}

impl Default for GpuFlatRound1StaticDesc {
    fn default() -> Self {
        Self {
            base_sources: [GpuFlatBaseAfterOneSourceEntry::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            c0_only_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_C0_ONLY_LINEAR],
            num_c0_only_linear: 0,
            unified_quadratic: [GpuFlatC1Pair::default(); FLAT_CONT_MAX_UNIFIED_QUADRATIC],
            num_unified_quadratic: 0,
            unified_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_UNIFIED_LINEAR],
            num_unified_linear: 0,
            num_constants: 0,
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

/// Round 2 static description: mixed base_after_two + continuing sources.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuFlatRound2StaticDesc {
    pub(super) base_sources: [GpuFlatBaseAfterTwoSourceEntry; FLAT_CONT_MAX_BASE_SOURCES],
    pub(super) num_base_sources: u32,
    pub(super) ext_sources: [GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_EXT_SOURCES],
    pub(super) num_ext_sources: u32,

    pub(super) c0_only_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_C0_ONLY_LINEAR],
    pub(super) num_c0_only_linear: u32,
    pub(super) unified_quadratic: [GpuFlatC1Pair; FLAT_CONT_MAX_UNIFIED_QUADRATIC],
    pub(super) num_unified_quadratic: u32,
    pub(super) unified_linear: [GpuFlatC0Ref; FLAT_CONT_MAX_UNIFIED_LINEAR],
    pub(super) num_unified_linear: u32,
    pub(super) num_constants: u32,
}

unsafe impl Send for GpuFlatRound2StaticDesc {}
unsafe impl Sync for GpuFlatRound2StaticDesc {}

impl Default for GpuFlatRound2StaticDesc {
    fn default() -> Self {
        Self {
            base_sources: [GpuFlatBaseAfterTwoSourceEntry::default(); FLAT_CONT_MAX_BASE_SOURCES],
            num_base_sources: 0,
            ext_sources: [GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_EXT_SOURCES],
            num_ext_sources: 0,
            c0_only_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_C0_ONLY_LINEAR],
            num_c0_only_linear: 0,
            unified_quadratic: [GpuFlatC1Pair::default(); FLAT_CONT_MAX_UNIFIED_QUADRATIC],
            num_unified_quadratic: 0,
            unified_linear: [GpuFlatC0Ref::default(); FLAT_CONT_MAX_UNIFIED_LINEAR],
            num_unified_linear: 0,
            num_constants: 0,
        }
    }
}

// ===========================================================================
// Round 1 kernel declarations and launch
// ===========================================================================

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1FlatCompact<T>,
    static_desc: GpuFlatRound1StaticDesc,
    coefficients: *const T,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round1_flat_compact_e4_kernel(
        static_desc: GpuFlatRound1StaticDesc,
        coefficients: *const E4,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1FlatExplicit<T>,
    static_desc: GpuFlatRound1StaticDesc,
    coefficients: *const T,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round1_flat_explicit_e4_kernel(
        static_desc: GpuFlatRound1StaticDesc,
        coefficients: *const E4,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1FlatConstantCompact<T>,
    static_desc: GpuFlatRound1StaticDesc,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round1_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatRound1StaticDesc,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound1FlatConstantExplicit<T>,
    static_desc: GpuFlatRound1StaticDesc,
    folding_challenge: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round1_flat_constant_explicit_e4_kernel(
        static_desc: GpuFlatRound1StaticDesc,
        folding_challenge: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(super) fn launch_main_round1_flat(
    static_desc: &GpuFlatRound1StaticDesc,
    coefficients: *const E4,
    folding_challenge: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound1FlatExplicitArguments::new(
            *static_desc,
            coefficients,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound1FlatExplicitFunction(ab_gkr_main_round1_flat_explicit_e4_kernel)
            .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound1FlatCompactArguments::new(
            *static_desc,
            coefficients,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound1FlatCompactFunction(ab_gkr_main_round1_flat_compact_e4_kernel)
            .launch(&config, &args)
    }
}

pub(super) fn launch_main_round1_flat_constant(
    static_desc: &GpuFlatRound1StaticDesc,
    folding_challenge: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound1FlatConstantExplicitArguments::new(
            *static_desc,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound1FlatConstantExplicitFunction(
            ab_gkr_main_round1_flat_constant_explicit_e4_kernel,
        )
        .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound1FlatConstantCompactArguments::new(
            *static_desc,
            folding_challenge,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound1FlatConstantCompactFunction(
            ab_gkr_main_round1_flat_constant_compact_e4_kernel,
        )
        .launch(&config, &args)
    }
}

// ===========================================================================
// Round 2 kernel declarations and launch
// ===========================================================================

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2FlatCompact<T>,
    static_desc: GpuFlatRound2StaticDesc,
    coefficients: *const T,
    folding_challenges: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round2_flat_compact_e4_kernel(
        static_desc: GpuFlatRound2StaticDesc,
        coefficients: *const E4,
        folding_challenges: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2FlatExplicit<T>,
    static_desc: GpuFlatRound2StaticDesc,
    coefficients: *const T,
    folding_challenges: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round2_flat_explicit_e4_kernel(
        static_desc: GpuFlatRound2StaticDesc,
        coefficients: *const E4,
        folding_challenges: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2FlatConstantCompact<T>,
    static_desc: GpuFlatRound2StaticDesc,
    folding_challenges: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round2_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatRound2StaticDesc,
        folding_challenges: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRMainRound2FlatConstantExplicit<T>,
    static_desc: GpuFlatRound2StaticDesc,
    folding_challenges: *const T,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_gkr_main_round2_flat_constant_explicit_e4_kernel(
        static_desc: GpuFlatRound2StaticDesc,
        folding_challenges: *const E4,
        fold_stride: u32,
        next_layer_size: u32,
        eq_values: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(super) fn launch_main_round2_flat(
    static_desc: &GpuFlatRound2StaticDesc,
    coefficients: *const E4,
    folding_challenges: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound2FlatExplicitArguments::new(
            *static_desc,
            coefficients,
            folding_challenges,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound2FlatExplicitFunction(ab_gkr_main_round2_flat_explicit_e4_kernel)
            .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound2FlatCompactArguments::new(
            *static_desc,
            coefficients,
            folding_challenges,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound2FlatCompactFunction(ab_gkr_main_round2_flat_compact_e4_kernel)
            .launch(&config, &args)
    }
}

pub(super) fn launch_main_round2_flat_constant(
    static_desc: &GpuFlatRound2StaticDesc,
    folding_challenges: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_values: *const E4,
    contributions: *mut E4,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    if explicit_form {
        let args = GpuGKRMainRound2FlatConstantExplicitArguments::new(
            *static_desc,
            folding_challenges,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound2FlatConstantExplicitFunction(
            ab_gkr_main_round2_flat_constant_explicit_e4_kernel,
        )
        .launch(&config, &args)
    } else {
        let args = GpuGKRMainRound2FlatConstantCompactArguments::new(
            *static_desc,
            folding_challenges,
            fold_stride,
            next_layer_size,
            eq_values,
            contributions,
            acc_size,
        );
        GpuGKRMainRound2FlatConstantCompactFunction(
            ab_gkr_main_round2_flat_constant_compact_e4_kernel,
        )
        .launch(&config, &args)
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
        constraint_batch: E4,
    ) -> Vec<E4> {
        plan.recipes
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

    fn cont_source(cache_ptr: *mut E4) -> GpuExtensionFieldPolyContinuingSourcePlan<E4> {
        GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: std::ptr::null(),
            this_layer_start: cache_ptr,
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: false,
        }
    }

    struct Round1BaseCpu {
        values: Vec<BF>,
        base_layer_half_size: usize,
        next_layer_size: usize,
    }

    struct Round2BaseCpu {
        values: Vec<BF>,
        base_layer_half_size: usize,
        base_quarter_size: usize,
        next_layer_size: usize,
    }

    struct ExtCpu {
        values: Vec<E4>,
    }

    fn fold_ext_value(values: &[E4], fold_stride: usize, idx: usize, challenge: E4) -> E4 {
        let f0 = values[idx];
        let f1 = values[fold_stride + idx];
        let mut diff = f1;
        diff.sub_assign(&f0);
        let mut result = challenge;
        result.mul_assign(&diff);
        result.add_assign(&f0);
        result
    }

    fn load_ext_pair(
        values: &[E4],
        fold_stride: usize,
        next_layer_size: usize,
        gid: usize,
        challenge: E4,
        explicit: bool,
    ) -> (E4, E4) {
        let f0 = fold_ext_value(values, fold_stride, gid, challenge);
        let f1 = fold_ext_value(values, fold_stride, next_layer_size + gid, challenge);
        if explicit {
            (f0, f1)
        } else {
            let mut delta = f1;
            delta.sub_assign(&f0);
            (f0, delta)
        }
    }

    fn base_after_one_value(
        values: &[BF],
        base_layer_half_size: usize,
        idx: usize,
        challenge: E4,
    ) -> E4 {
        let f0 = values[idx];
        let f1 = values[base_layer_half_size + idx];
        let mut diff = f1;
        diff.sub_assign(&f0);
        let mut result = challenge;
        result.mul_assign_by_base(&diff);
        result.add_assign_base(&f0);
        result
    }

    fn load_base_after_one_pair(
        values: &[BF],
        base_layer_half_size: usize,
        next_layer_size: usize,
        gid: usize,
        challenge: E4,
        explicit: bool,
    ) -> (E4, E4) {
        let f0 = base_after_one_value(values, base_layer_half_size, gid, challenge);
        let f1 = base_after_one_value(
            values,
            base_layer_half_size,
            next_layer_size + gid,
            challenge,
        );
        if explicit {
            (f0, f1)
        } else {
            let mut delta = f1;
            delta.sub_assign(&f0);
            (f0, delta)
        }
    }

    fn base_after_two_value(
        values: &[BF],
        base_layer_half_size: usize,
        base_quarter_size: usize,
        idx: usize,
        first_challenge: E4,
        second_challenge: E4,
    ) -> E4 {
        let f00 = values[idx];
        let f01 = values[base_layer_half_size + idx];
        let f10 = values[base_quarter_size + idx];
        let f11 = values[base_layer_half_size + base_quarter_size + idx];

        let mut c01 = f01;
        c01.sub_assign(&f00);
        let mut c10 = f10;
        c10.sub_assign(&f00);
        let mut c11 = f00;
        c11.sub_assign(&f01);
        c11.sub_assign(&f10);
        c11.add_assign(&f11);

        let mut result = first_challenge;
        result.mul_assign_by_base(&c01);
        let mut term = second_challenge;
        term.mul_assign_by_base(&c10);
        result.add_assign(&term);
        let mut combined = first_challenge;
        combined.mul_assign(&second_challenge);
        combined.mul_assign_by_base(&c11);
        result.add_assign(&combined);
        result.add_assign_base(&f00);
        result
    }

    fn load_base_after_two_pair(
        values: &[BF],
        base_layer_half_size: usize,
        base_quarter_size: usize,
        next_layer_size: usize,
        gid: usize,
        first_challenge: E4,
        second_challenge: E4,
        explicit: bool,
    ) -> (E4, E4) {
        let f0 = base_after_two_value(
            values,
            base_layer_half_size,
            base_quarter_size,
            gid,
            first_challenge,
            second_challenge,
        );
        let f1 = base_after_two_value(
            values,
            base_layer_half_size,
            base_quarter_size,
            next_layer_size + gid,
            first_challenge,
            second_challenge,
        );
        if explicit {
            (f0, f1)
        } else {
            let mut delta = f1;
            delta.sub_assign(&f0);
            (f0, delta)
        }
    }

    fn eval_round1_cpu(
        desc: &GpuFlatRound1StaticDesc,
        coeffs: &[E4],
        base_sources: &[Round1BaseCpu],
        ext_sources: &[ExtCpu],
        folding_challenge: E4,
        fold_stride: usize,
        next_layer_size: usize,
        eq_values: &[E4],
        acc_size: usize,
        explicit: bool,
    ) -> Vec<E4> {
        let mut output = vec![E4::ZERO; acc_size * 2];
        for gid in 0..acc_size {
            let mut c0 = E4::ZERO;
            let mut c1 = E4::ZERO;
            let mut coeff_idx = 0usize;

            for _ in 0..desc.num_constants as usize {
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                c0.add_assign(&k);
                if explicit {
                    c1.add_assign(&k);
                }
            }

            for i in 0..desc.num_c0_only_linear as usize {
                let source_idx = desc.c0_only_linear[i].source_idx;
                let (f0, f1) = if source_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (source_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                } else {
                    let idx = source_idx as usize;
                    let src = &base_sources[idx];
                    load_base_after_one_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                if explicit {
                    let mut term1 = k;
                    term1.mul_assign(&f1);
                    c1.add_assign(&term1);
                }
            }

            for i in 0..desc.num_unified_quadratic as usize {
                let t = desc.unified_quadratic[i];
                let (a0, a1) = if t.source_a & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (t.source_a & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                } else {
                    let idx = t.source_a as usize;
                    let src = &base_sources[idx];
                    load_base_after_one_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                };
                let (b0, b1) = if t.source_b & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (t.source_b & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                } else {
                    let idx = t.source_b as usize;
                    let src = &base_sources[idx];
                    load_base_after_one_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut prod0 = a0;
                prod0.mul_assign(&b0);
                let mut term0 = k;
                term0.mul_assign(&prod0);
                c0.add_assign(&term0);
                let mut prod1 = a1;
                prod1.mul_assign(&b1);
                let mut term1 = k;
                term1.mul_assign(&prod1);
                c1.add_assign(&term1);
            }

            for i in 0..desc.num_unified_linear as usize {
                let source_idx = desc.unified_linear[i].source_idx;
                let (f0, f1) = if source_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (source_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                } else {
                    let idx = source_idx as usize;
                    let src = &base_sources[idx];
                    load_base_after_one_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.next_layer_size,
                        gid,
                        folding_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                let mut term1 = k;
                term1.mul_assign(&f1);
                c1.add_assign(&term1);
            }

            let mut out0 = c0;
            out0.mul_assign(&eq_values[gid]);
            let mut out1 = c1;
            out1.mul_assign(&eq_values[gid]);
            output[gid] = out0;
            output[acc_size + gid] = out1;
        }
        output
    }

    fn eval_round2_cpu(
        desc: &GpuFlatRound2StaticDesc,
        coeffs: &[E4],
        base_sources: &[Round2BaseCpu],
        ext_sources: &[ExtCpu],
        first_challenge: E4,
        second_challenge: E4,
        fold_stride: usize,
        next_layer_size: usize,
        eq_values: &[E4],
        acc_size: usize,
        explicit: bool,
    ) -> Vec<E4> {
        let mut output = vec![E4::ZERO; acc_size * 2];
        for gid in 0..acc_size {
            let mut c0 = E4::ZERO;
            let mut c1 = E4::ZERO;
            let mut coeff_idx = 0usize;

            for _ in 0..desc.num_constants as usize {
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                c0.add_assign(&k);
                if explicit {
                    c1.add_assign(&k);
                }
            }

            for i in 0..desc.num_c0_only_linear as usize {
                let source_idx = desc.c0_only_linear[i].source_idx;
                let (f0, f1) = if source_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (source_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        second_challenge,
                        explicit,
                    )
                } else {
                    let idx = source_idx as usize;
                    let src = &base_sources[idx];
                    load_base_after_two_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.base_quarter_size,
                        src.next_layer_size,
                        gid,
                        first_challenge,
                        second_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                if explicit {
                    let mut term1 = k;
                    term1.mul_assign(&f1);
                    c1.add_assign(&term1);
                }
            }

            for i in 0..desc.num_unified_quadratic as usize {
                let t = desc.unified_quadratic[i];
                let (a0, a1) = if t.source_a & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (t.source_a & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        second_challenge,
                        explicit,
                    )
                } else {
                    let idx = t.source_a as usize;
                    let src = &base_sources[idx];
                    load_base_after_two_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.base_quarter_size,
                        src.next_layer_size,
                        gid,
                        first_challenge,
                        second_challenge,
                        explicit,
                    )
                };
                let (b0, b1) = if t.source_b & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (t.source_b & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        second_challenge,
                        explicit,
                    )
                } else {
                    let idx = t.source_b as usize;
                    let src = &base_sources[idx];
                    load_base_after_two_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.base_quarter_size,
                        src.next_layer_size,
                        gid,
                        first_challenge,
                        second_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut prod0 = a0;
                prod0.mul_assign(&b0);
                let mut term0 = k;
                term0.mul_assign(&prod0);
                c0.add_assign(&term0);
                let mut prod1 = a1;
                prod1.mul_assign(&b1);
                let mut term1 = k;
                term1.mul_assign(&prod1);
                c1.add_assign(&term1);
            }

            for i in 0..desc.num_unified_linear as usize {
                let source_idx = desc.unified_linear[i].source_idx;
                let (f0, f1) = if source_idx & FLAT_CONT_EXT_SOURCE_BIT != 0 {
                    let idx = (source_idx & !FLAT_CONT_EXT_SOURCE_BIT) as usize;
                    load_ext_pair(
                        &ext_sources[idx].values,
                        fold_stride,
                        next_layer_size,
                        gid,
                        second_challenge,
                        explicit,
                    )
                } else {
                    let idx = source_idx as usize;
                    let src = &base_sources[idx];
                    load_base_after_two_pair(
                        &src.values,
                        src.base_layer_half_size,
                        src.base_quarter_size,
                        src.next_layer_size,
                        gid,
                        first_challenge,
                        second_challenge,
                        explicit,
                    )
                };
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                let mut term1 = k;
                term1.mul_assign(&f1);
                c1.add_assign(&term1);
            }

            let mut out0 = c0;
            out0.mul_assign(&eq_values[gid]);
            let mut out1 = c1;
            out1.mul_assign(&eq_values[gid]);
            output[gid] = out0;
            output[acc_size + gid] = out1;
        }
        output
    }

    fn eval_round3_cpu(
        desc: &GpuFlatContinuationStaticDesc,
        coeffs: &[E4],
        sources: &[ExtCpu],
        folding_challenge: E4,
        fold_stride: usize,
        next_layer_size: usize,
        eq_values: &[E4],
        acc_size: usize,
        explicit: bool,
    ) -> Vec<E4> {
        let mut output = vec![E4::ZERO; acc_size * 2];
        for gid in 0..acc_size {
            let mut c0 = E4::ZERO;
            let mut c1 = E4::ZERO;
            let mut coeff_idx = 0usize;

            for _ in 0..desc.num_constants as usize {
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                c0.add_assign(&k);
                if explicit {
                    c1.add_assign(&k);
                }
            }

            for i in 0..desc.num_c0_only_linear as usize {
                let idx = desc.c0_only_linear[i].source_idx as usize;
                let (f0, f1) = load_ext_pair(
                    &sources[idx].values,
                    fold_stride,
                    next_layer_size,
                    gid,
                    folding_challenge,
                    explicit,
                );
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                if explicit {
                    let mut term1 = k;
                    term1.mul_assign(&f1);
                    c1.add_assign(&term1);
                }
            }

            for i in 0..desc.num_unified_quadratic as usize {
                let t = desc.unified_quadratic[i];
                let (a0, a1) = load_ext_pair(
                    &sources[t.source_a as usize].values,
                    fold_stride,
                    next_layer_size,
                    gid,
                    folding_challenge,
                    explicit,
                );
                let (b0, b1) = load_ext_pair(
                    &sources[t.source_b as usize].values,
                    fold_stride,
                    next_layer_size,
                    gid,
                    folding_challenge,
                    explicit,
                );
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut prod0 = a0;
                prod0.mul_assign(&b0);
                let mut term0 = k;
                term0.mul_assign(&prod0);
                c0.add_assign(&term0);
                let mut prod1 = a1;
                prod1.mul_assign(&b1);
                let mut term1 = k;
                term1.mul_assign(&prod1);
                c1.add_assign(&term1);
            }

            for i in 0..desc.num_unified_linear as usize {
                let idx = desc.unified_linear[i].source_idx as usize;
                let (f0, f1) = load_ext_pair(
                    &sources[idx].values,
                    fold_stride,
                    next_layer_size,
                    gid,
                    folding_challenge,
                    explicit,
                );
                let k = coeffs[coeff_idx];
                coeff_idx += 1;
                let mut term0 = k;
                term0.mul_assign(&f0);
                c0.add_assign(&term0);
                let mut term1 = k;
                term1.mul_assign(&f1);
                c1.add_assign(&term1);
            }

            let mut out0 = c0;
            out0.mul_assign(&eq_values[gid]);
            let mut out1 = c1;
            out1.mul_assign(&eq_values[gid]);
            output[gid] = out0;
            output[acc_size + gid] = out1;
        }
        output
    }

    fn build_round1_desc_from_plan(
        plan: &FlatContinuationBuildPlan<E4>,
        base_sources: &[Vec<GpuFlatBaseAfterOneSourceEntry>],
        ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
    ) -> GpuFlatRound1StaticDesc {
        let mut desc = GpuFlatRound1StaticDesc::default();
        desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize].copy_from_slice(
            &plan.term_desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize],
        );
        desc.num_c0_only_linear = plan.term_desc.num_c0_only_linear;
        desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize].copy_from_slice(
            &plan.term_desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize],
        );
        desc.num_unified_quadratic = plan.term_desc.num_unified_quadratic;
        desc.unified_linear[..plan.term_desc.num_unified_linear as usize].copy_from_slice(
            &plan.term_desc.unified_linear[..plan.term_desc.num_unified_linear as usize],
        );
        desc.num_unified_linear = plan.term_desc.num_unified_linear;
        desc.num_constants = plan.term_desc.num_constants;

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

        for i in 0..desc.num_c0_only_linear as usize {
            desc.c0_only_linear[i].source_idx =
                idx_remap[desc.c0_only_linear[i].source_idx as usize];
        }
        for i in 0..desc.num_unified_quadratic as usize {
            desc.unified_quadratic[i].source_a =
                idx_remap[desc.unified_quadratic[i].source_a as usize];
            desc.unified_quadratic[i].source_b =
                idx_remap[desc.unified_quadratic[i].source_b as usize];
        }
        for i in 0..desc.num_unified_linear as usize {
            desc.unified_linear[i].source_idx =
                idx_remap[desc.unified_linear[i].source_idx as usize];
        }

        desc
    }

    fn build_round2_desc_from_plan(
        plan: &FlatContinuationBuildPlan<E4>,
        base_sources: &[Vec<GpuFlatBaseAfterTwoSourceEntry>],
        ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
    ) -> GpuFlatRound2StaticDesc {
        let mut desc = GpuFlatRound2StaticDesc::default();
        desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize].copy_from_slice(
            &plan.term_desc.c0_only_linear[..plan.term_desc.num_c0_only_linear as usize],
        );
        desc.num_c0_only_linear = plan.term_desc.num_c0_only_linear;
        desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize].copy_from_slice(
            &plan.term_desc.unified_quadratic[..plan.term_desc.num_unified_quadratic as usize],
        );
        desc.num_unified_quadratic = plan.term_desc.num_unified_quadratic;
        desc.unified_linear[..plan.term_desc.num_unified_linear as usize].copy_from_slice(
            &plan.term_desc.unified_linear[..plan.term_desc.num_unified_linear as usize],
        );
        desc.num_unified_linear = plan.term_desc.num_unified_linear;
        desc.num_constants = plan.term_desc.num_constants;

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

        for i in 0..desc.num_c0_only_linear as usize {
            desc.c0_only_linear[i].source_idx =
                idx_remap[desc.c0_only_linear[i].source_idx as usize];
        }
        for i in 0..desc.num_unified_quadratic as usize {
            desc.unified_quadratic[i].source_a =
                idx_remap[desc.unified_quadratic[i].source_a as usize];
            desc.unified_quadratic[i].source_b =
                idx_remap[desc.unified_quadratic[i].source_b as usize];
        }
        for i in 0..desc.num_unified_linear as usize {
            desc.unified_linear[i].source_idx =
                idx_remap[desc.unified_linear[i].source_idx as usize];
        }

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
        let quad = desc.unified_quadratic[0];
        assert_eq!(quad.source_a & FLAT_CONT_EXT_SOURCE_BIT, 0);
        assert_ne!(quad.source_b & FLAT_CONT_EXT_SOURCE_BIT, 0);
        let lin = desc.c0_only_linear[0].source_idx;
        assert_eq!(lin & FLAT_CONT_EXT_SOURCE_BIT, 0);
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
        let quad = desc.unified_quadratic[0];
        assert_eq!(quad.source_a & FLAT_CONT_EXT_SOURCE_BIT, 0);
        assert_ne!(quad.source_b & FLAT_CONT_EXT_SOURCE_BIT, 0);
        let lin = desc.c0_only_linear[0].source_idx;
        assert_eq!(lin & FLAT_CONT_EXT_SOURCE_BIT, 0);
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

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_mixed_sources_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values: Vec<BF> = (0..8).map(|i| BF::new(10 + i)).collect();
        let ext_values: Vec<E4> = (0..8).map(|i| sample_ext(100 + i * 3)).collect();

        let base_input_dev = alloc_and_copy(&context, &base_values);
        let ext_prev_dev = alloc_and_copy(&context, &ext_values);
        let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let mut desc = GpuFlatRound1StaticDesc::default();
        desc.base_sources[0] = GpuFlatBaseAfterOneSourceEntry {
            base_layer_half_size: 4,
            next_layer_size: 2,
            base_input_start: base_input_dev.as_ptr().cast(),
            this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        };
        desc.ext_sources[0] = GpuFlatContinuingSourceEntry {
            previous_layer_start: ext_prev_dev.as_ptr().cast(),
            this_layer_cache_start: ext_cache.as_ptr().cast_mut().cast(),
        };
        desc.num_base_sources = 1;
        desc.num_ext_sources = 1;
        desc.num_constants = 1;
        desc.c0_only_linear[0] = GpuFlatC0Ref { source_idx: 0 };
        desc.num_c0_only_linear = 1;
        desc.unified_quadratic[0] = GpuFlatC1Pair {
            source_a: 0,
            source_b: FLAT_CONT_EXT_SOURCE_BIT,
        };
        desc.num_unified_quadratic = 1;
        desc.unified_linear[0] = GpuFlatC0Ref {
            source_idx: FLAT_CONT_EXT_SOURCE_BIT,
        };
        desc.num_unified_linear = 1;

        let coeffs = vec![
            sample_ext(11),
            sample_ext(13),
            sample_ext(17),
            sample_ext(19),
        ];
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let folding_challenge = sample_ext(42);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(7), sample_ext(9)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![Round1BaseCpu {
            values: base_values,
            base_layer_half_size: 4,
            next_layer_size: 2,
        }];
        let cpu_ext = vec![ExtCpu { values: ext_values }];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(actual, expected, "flat round1 mixed sources mismatch");
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_deferred_constraint_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base0_values: Vec<BF> = (0..8).map(|i| BF::new(20 + i)).collect();
        let base1_values: Vec<BF> = (0..8).map(|i| BF::new(40 + i)).collect();
        let base2_values: Vec<BF> = (0..8).map(|i| BF::new(60 + i)).collect();

        let base0_dev = alloc_and_copy(&context, &base0_values);
        let base1_dev = alloc_and_copy(&context, &base1_values);
        let base2_dev = alloc_and_copy(&context, &base2_values);

        let base0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base2_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base0_dev.as_ptr().cast(),
                this_layer_cache_start: base0_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base1_dev.as_ptr().cast(),
                this_layer_cache_start: base1_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base2_dev.as_ptr().cast(),
                this_layer_cache_start: base2_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy2: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy0.as_ptr(),
                this_layer_start: dummy0.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy2.as_ptr(),
                this_layer_start: dummy2.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let constraint_template = GpuGKRMainLayerConstraintTemplate {
            quadratic_terms: vec![GpuGKRMainLayerConstraintQuadraticTemplate {
                lhs: 0,
                rhs: 1,
                challenge_terms: vec![],
            }],
            linear_terms: vec![
                GpuGKRMainLayerConstraintLinearTemplate {
                    input: 2,
                    challenge_terms: vec![],
                },
                GpuGKRMainLayerConstraintLinearTemplate {
                    input: NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
                    challenge_terms: vec![],
                },
            ],
            constant_terms: vec![GpuGKRMainLayerConstraintChallengeTerm {
                coeff: BF::ONE,
                source: GpuGKRMainLayerDeferredChallengeSource::ConstraintBatch,
                power: 0,
            }],
        };
        let constraint_source =
            GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_template);

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &[],
            batch_challenge_power_offset: 1,
            constraint_source: Some(&constraint_source),
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(5);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, E4::ZERO, E4::ONE);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc = build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[vec![]]);
        let expected_len = desc.num_constants as usize
            + desc.num_c0_only_linear as usize
            + desc.num_unified_quadratic as usize
            + desc.num_unified_linear as usize;
        assert_eq!(coeffs.len(), expected_len, "round1 deferred coeff count");

        let folding_challenge = sample_ext(90);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(3), sample_ext(4)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            false,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round1BaseCpu {
                values: base0_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base1_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base2_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &[],
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            false,
        );

        assert_eq!(actual, expected, "flat round1 deferred constraint mismatch");
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_lookup_base_pair_gamma_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base0_values: Vec<BF> = (0..8).map(|i| BF::new(11 + i)).collect();
        let base1_values: Vec<BF> = (0..8).map(|i| BF::new(31 + i)).collect();

        let base0_dev = alloc_and_copy(&context, &base0_values);
        let base1_dev = alloc_and_copy(&context, &base1_values);

        let base0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base0_dev.as_ptr().cast(),
                this_layer_cache_start: base0_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base1_dev.as_ptr().cast(),
                this_layer_cache_start: base1_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy0.as_ptr(),
                this_layer_start: dummy0.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupBasePair,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &[],
            batch_challenge_power_offset: 2,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(5);
        let lookup_additive = sample_ext(9);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, lookup_additive, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc = build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[vec![]]);

        let folding_challenge = sample_ext(77);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(3), sample_ext(4)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round1BaseCpu {
                values: base0_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base1_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &[],
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(
            actual, expected,
            "flat round1 lookup base pair gamma mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_lookup_base_minus_multiplicity_gamma_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base0_values: Vec<BF> = (0..8).map(|i| BF::new(21 + i)).collect();
        let base1_values: Vec<BF> = (0..8).map(|i| BF::new(41 + i)).collect();
        let base2_values: Vec<BF> = (0..8).map(|i| BF::new(61 + i)).collect();

        let base0_dev = alloc_and_copy(&context, &base0_values);
        let base1_dev = alloc_and_copy(&context, &base1_values);
        let base2_dev = alloc_and_copy(&context, &base2_values);

        let base0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base2_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base0_dev.as_ptr().cast(),
                this_layer_cache_start: base0_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base1_dev.as_ptr().cast(),
                this_layer_cache_start: base1_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base2_dev.as_ptr().cast(),
                this_layer_cache_start: base2_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy2: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy0.as_ptr(),
                this_layer_start: dummy0.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy2.as_ptr(),
                this_layer_start: dummy2.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &[],
            batch_challenge_power_offset: 1,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(6);
        let lookup_additive = sample_ext(12);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, lookup_additive, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc = build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[vec![]]);

        let folding_challenge = sample_ext(81);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(5), sample_ext(7)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round1BaseCpu {
                values: base0_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base1_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base2_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &[],
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(
            actual, expected,
            "flat round1 lookup base minus multiplicity gamma mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_lookup_ext_minus_multiplicity_gamma_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values: Vec<BF> = (0..8).map(|i| BF::new(13 + i)).collect();
        let ext0_values: Vec<E4> = (0..8).map(|i| sample_ext(200 + i * 2)).collect();
        let ext1_values: Vec<E4> = (0..8).map(|i| sample_ext(250 + i * 3)).collect();

        let base_dev = alloc_and_copy(&context, &base_values);
        let ext0_dev = alloc_and_copy(&context, &ext0_values);
        let ext1_dev = alloc_and_copy(&context, &ext1_values);

        let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![GpuFlatBaseAfterOneSourceEntry {
            base_layer_half_size: 4,
            next_layer_size: 2,
            base_input_start: base_dev.as_ptr().cast(),
            this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }];
        let ext_sources = vec![
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext0_dev.as_ptr().cast(),
                this_layer_cache_start: ext0_cache.as_ptr().cast_mut().cast(),
            },
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext1_dev.as_ptr().cast(),
                this_layer_cache_start: ext1_cache.as_ptr().cast_mut().cast(),
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy2: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: dummy0.as_ptr(),
            this_layer_start: dummy0.as_ptr().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: true,
        }];
        let plan_ext_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy2.as_ptr(),
                this_layer_start: dummy2.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &plan_ext_inputs,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(4);
        let lookup_additive = sample_ext(14);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, lookup_additive, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc =
            build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[ext_sources.clone()]);

        let folding_challenge = sample_ext(67);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(11), sample_ext(12)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![Round1BaseCpu {
            values: base_values,
            base_layer_half_size: 4,
            next_layer_size: 2,
        }];
        let cpu_ext = vec![
            ExtCpu {
                values: ext0_values,
            },
            ExtCpu {
                values: ext1_values,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(
            actual, expected,
            "flat round1 lookup ext minus multiplicity gamma mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_lookup_unbalanced_gamma_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values: Vec<BF> = (0..8).map(|i| BF::new(17 + i)).collect();
        let ext0_values: Vec<E4> = (0..8).map(|i| sample_ext(310 + i * 2)).collect();
        let ext1_values: Vec<E4> = (0..8).map(|i| sample_ext(350 + i * 2)).collect();

        let base_dev = alloc_and_copy(&context, &base_values);
        let ext0_dev = alloc_and_copy(&context, &ext0_values);
        let ext1_dev = alloc_and_copy(&context, &ext1_values);

        let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![GpuFlatBaseAfterOneSourceEntry {
            base_layer_half_size: 4,
            next_layer_size: 2,
            base_input_start: base_dev.as_ptr().cast(),
            this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }];
        let ext_sources = vec![
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext0_dev.as_ptr().cast(),
                this_layer_cache_start: ext0_cache.as_ptr().cast_mut().cast(),
            },
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext1_dev.as_ptr().cast(),
                this_layer_cache_start: ext1_cache.as_ptr().cast_mut().cast(),
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy2: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start: dummy0.as_ptr(),
            this_layer_start: dummy0.as_ptr().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: true,
        }];
        let plan_ext_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy2.as_ptr(),
                this_layer_start: dummy2.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &plan_ext_inputs,
            batch_challenge_power_offset: 3,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(9);
        let lookup_additive = sample_ext(15);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, lookup_additive, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc =
            build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[ext_sources.clone()]);

        let folding_challenge = sample_ext(91);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(13), sample_ext(17)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![Round1BaseCpu {
            values: base_values,
            base_layer_half_size: 4,
            next_layer_size: 2,
        }];
        let cpu_ext = vec![
            ExtCpu {
                values: ext0_values,
            },
            ExtCpu {
                values: ext1_values,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(
            actual, expected,
            "flat round1 lookup unbalanced gamma mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round1_lookup_cached_dens_and_setup_gamma_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base0_values: Vec<BF> = (0..8).map(|i| BF::new(19 + i)).collect();
        let base1_values: Vec<BF> = (0..8).map(|i| BF::new(29 + i)).collect();
        let ext0_values: Vec<E4> = (0..8).map(|i| sample_ext(410 + i * 2)).collect();
        let ext1_values: Vec<E4> = (0..8).map(|i| sample_ext(470 + i * 2)).collect();

        let base0_dev = alloc_and_copy(&context, &base0_values);
        let base1_dev = alloc_and_copy(&context, &base1_values);
        let ext0_dev = alloc_and_copy(&context, &ext0_values);
        let ext1_dev = alloc_and_copy(&context, &ext1_values);

        let base0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let base1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext0_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext1_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_sources = vec![
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base0_dev.as_ptr().cast(),
                this_layer_cache_start: base0_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterOneSourceEntry {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: base1_dev.as_ptr().cast(),
                this_layer_cache_start: base1_cache.as_ptr().cast_mut().cast(),
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ];
        let ext_sources = vec![
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext0_dev.as_ptr().cast(),
                this_layer_cache_start: ext0_cache.as_ptr().cast_mut().cast(),
            },
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext1_dev.as_ptr().cast(),
                this_layer_cache_start: ext1_cache.as_ptr().cast_mut().cast(),
            },
        ];

        let dummy0: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy1: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy2: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let dummy3: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
        let plan_base_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy0.as_ptr(),
                this_layer_start: dummy0.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy1.as_ptr(),
                this_layer_start: dummy1.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];
        let plan_ext_inputs = vec![
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy2.as_ptr(),
                this_layer_start: dummy2.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: dummy3.as_ptr(),
                this_layer_start: dummy3.as_ptr().cast_mut(),
                this_layer_size: 0,
                next_layer_size: 0,
                first_access: true,
            },
        ];

        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
            gate_idx: 0,
            base_inputs: &plan_base_inputs,
            ext_inputs: &plan_ext_inputs,
            batch_challenge_power_offset: 1,
            constraint_source: None,
        };
        let plan = build_flat_continuation_plan(&[gate]);

        let batch_challenge_base = sample_ext(8);
        let lookup_additive = sample_ext(18);
        let coeffs = plan.resolve_all(batch_challenge_base, E4::ZERO, lookup_additive, E4::ZERO);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let desc =
            build_round1_desc_from_plan(&plan, &[base_sources.clone()], &[ext_sources.clone()]);

        let folding_challenge = sample_ext(95);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(19), sample_ext(23)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round1_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round1BaseCpu {
                values: base0_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
            Round1BaseCpu {
                values: base1_values,
                base_layer_half_size: 4,
                next_layer_size: 2,
            },
        ];
        let cpu_ext = vec![
            ExtCpu {
                values: ext0_values,
            },
            ExtCpu {
                values: ext1_values,
            },
        ];
        let expected = eval_round1_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(
            actual, expected,
            "flat round1 lookup cached dens/setup gamma mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round2_mixed_sources_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values: Vec<BF> = (0..16).map(|i| BF::new(70 + i)).collect();
        let ext_values: Vec<E4> = (0..8).map(|i| sample_ext(500 + i * 2)).collect();

        let base_input_dev = alloc_and_copy(&context, &base_values);
        let ext_prev_dev = alloc_and_copy(&context, &ext_values);
        let base_cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let ext_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let mut desc = GpuFlatRound2StaticDesc::default();
        desc.base_sources[0] = GpuFlatBaseAfterTwoSourceEntry {
            base_input_start: base_input_dev.as_ptr().cast(),
            this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
            base_layer_half_size: 8,
            base_quarter_size: 4,
            next_layer_size: 2,
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        };
        desc.ext_sources[0] = GpuFlatContinuingSourceEntry {
            previous_layer_start: ext_prev_dev.as_ptr().cast(),
            this_layer_cache_start: ext_cache.as_ptr().cast_mut().cast(),
        };
        desc.num_base_sources = 1;
        desc.num_ext_sources = 1;
        desc.num_constants = 1;
        desc.c0_only_linear[0] = GpuFlatC0Ref { source_idx: 0 };
        desc.num_c0_only_linear = 1;
        desc.unified_quadratic[0] = GpuFlatC1Pair {
            source_a: 0,
            source_b: FLAT_CONT_EXT_SOURCE_BIT,
        };
        desc.num_unified_quadratic = 1;
        desc.unified_linear[0] = GpuFlatC0Ref {
            source_idx: FLAT_CONT_EXT_SOURCE_BIT,
        };
        desc.num_unified_linear = 1;

        let coeffs = vec![
            sample_ext(21),
            sample_ext(23),
            sample_ext(29),
            sample_ext(31),
        ];
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let first_challenge = sample_ext(123);
        let second_challenge = sample_ext(124);
        let folding_dev = alloc_and_copy(&context, &[first_challenge, second_challenge]);
        let eq_values = [sample_ext(15), sample_ext(16)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round2_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![Round2BaseCpu {
            values: base_values,
            base_layer_half_size: 8,
            base_quarter_size: 4,
            next_layer_size: 2,
        }];
        let cpu_ext = vec![ExtCpu { values: ext_values }];
        let expected = eval_round2_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            first_challenge,
            second_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(actual, expected, "flat round2 mixed sources mismatch");
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round2_lookup_from_vector_input_with_setup_compact_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values_c: Vec<BF> = (0..16).map(|i| BF::new(100 + i)).collect();
        let base_values_tail: Vec<BF> = (0..16).map(|i| BF::new(200 + i)).collect();
        let base_input_c = alloc_and_copy(&context, &base_values_c);
        let base_input_tail = alloc_and_copy(&context, &base_values_tail);
        let base_cache_c: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();
        let base_cache_tail: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();

        let base_inputs = [
            cont_source(base_cache_c.as_ptr() as *mut E4),
            cont_source(base_cache_tail.as_ptr() as *mut E4),
        ];
        let metadata = GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms: vec![GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 0,
                challenge: sample_ext(11),
            }],
            linear_terms: vec![GpuGKRMainLayerConstraintLinearTerm {
                input: 0,
                challenge: sample_ext(13),
            }],
            constant_offset: E4::ZERO,
        };
        let metadata_source = GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata);
        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &[],
            batch_challenge_power_offset: 0,
            constraint_source: Some(&metadata_source),
        };
        let plan = build_flat_continuation_plan(&[gate]);
        let coeffs = resolve_plan_coeffs(
            &plan,
            sample_ext(7),
            sample_ext(3),
            sample_ext(5),
            sample_ext(9),
        );

        let base_sources = vec![vec![
            GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_c.as_ptr().cast(),
                this_layer_cache_start: base_cache_c.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_tail.as_ptr().cast(),
                this_layer_cache_start: base_cache_tail.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ]];
        let ext_sources: Vec<Vec<GpuFlatContinuingSourceEntry>> = vec![vec![]];
        let desc = build_round2_desc_from_plan(&plan, &base_sources, &ext_sources);

        let first_challenge = sample_ext(101);
        let second_challenge = sample_ext(102);
        let folding_dev = alloc_and_copy(&context, &[first_challenge, second_challenge]);
        let eq_values = [sample_ext(15), sample_ext(16)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round2_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            false,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round2BaseCpu {
                values: base_values_c,
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
            },
            Round2BaseCpu {
                values: base_values_tail,
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
            },
        ];
        let cpu_ext: Vec<ExtCpu> = vec![];
        let expected = eval_round2_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            first_challenge,
            second_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            false,
        );

        assert_eq!(
            actual, expected,
            "flat round2 lookup-from-vector-with-setup compact mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round2_lookup_unbalanced_pair_with_vector_inputs_compact_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values_d: Vec<BF> = (0..16).map(|i| BF::new(300 + i)).collect();
        let base_input_d = alloc_and_copy(&context, &base_values_d);
        let base_cache_d: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();
        let ext_a_values: Vec<E4> = (0..8).map(|i| sample_ext(400 + i * 2)).collect();
        let ext_b_values: Vec<E4> = (0..8).map(|i| sample_ext(500 + i * 2)).collect();
        let ext_prev_a = alloc_and_copy(&context, &ext_a_values);
        let ext_prev_b = alloc_and_copy(&context, &ext_b_values);
        let ext_cache_a: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let ext_cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_inputs = [cont_source(base_cache_d.as_ptr() as *mut E4)];
        let ext_inputs = [
            cont_source(ext_cache_a.as_ptr() as *mut E4),
            cont_source(ext_cache_b.as_ptr() as *mut E4),
        ];
        let metadata = GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms: Vec::new(),
            linear_terms: vec![GpuGKRMainLayerConstraintLinearTerm {
                input: 0,
                challenge: sample_ext(17),
            }],
            constant_offset: E4::ZERO,
        };
        let metadata_source = GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata);
        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &ext_inputs,
            batch_challenge_power_offset: 0,
            constraint_source: Some(&metadata_source),
        };
        let plan = build_flat_continuation_plan(&[gate]);
        let coeffs = resolve_plan_coeffs(
            &plan,
            sample_ext(7),
            sample_ext(3),
            sample_ext(5),
            sample_ext(9),
        );

        let base_sources = vec![vec![GpuFlatBaseAfterTwoSourceEntry {
            base_input_start: base_input_d.as_ptr().cast(),
            this_layer_cache_start: base_cache_d.as_ptr().cast_mut().cast(),
            base_layer_half_size: 8,
            base_quarter_size: 4,
            next_layer_size: 2,
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }]];
        let ext_sources = vec![vec![
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext_prev_a.as_ptr().cast(),
                this_layer_cache_start: ext_cache_a.as_ptr().cast_mut().cast(),
            },
            GpuFlatContinuingSourceEntry {
                previous_layer_start: ext_prev_b.as_ptr().cast(),
                this_layer_cache_start: ext_cache_b.as_ptr().cast_mut().cast(),
            },
        ]];
        let desc = build_round2_desc_from_plan(&plan, &base_sources, &ext_sources);

        let first_challenge = sample_ext(201);
        let second_challenge = sample_ext(202);
        let folding_dev = alloc_and_copy(&context, &[first_challenge, second_challenge]);
        let eq_values = [sample_ext(25), sample_ext(26)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round2_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            false,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![Round2BaseCpu {
            values: base_values_d,
            base_layer_half_size: 8,
            base_quarter_size: 4,
            next_layer_size: 2,
        }];
        let cpu_ext = vec![
            ExtCpu {
                values: ext_a_values,
            },
            ExtCpu {
                values: ext_b_values,
            },
        ];
        let expected = eval_round2_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            first_challenge,
            second_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            false,
        );

        assert_eq!(
            actual, expected,
            "flat round2 lookup-unbalanced-pair-with-vector-inputs compact mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round2_lookup_with_dens_and_setup_expressions_compact_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let base_values_a: Vec<BF> = (0..16).map(|i| BF::new(600 + i)).collect();
        let base_values_c: Vec<BF> = (0..16).map(|i| BF::new(700 + i)).collect();
        let base_values_tail: Vec<BF> = (0..16).map(|i| BF::new(800 + i)).collect();
        let base_input_a = alloc_and_copy(&context, &base_values_a);
        let base_input_c = alloc_and_copy(&context, &base_values_c);
        let base_input_tail = alloc_and_copy(&context, &base_values_tail);
        let base_cache_a: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();
        let base_cache_c: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();
        let base_cache_tail: DeviceAllocation<E4> =
            context.alloc(8, AllocationPlacement::Top).unwrap();

        let base_inputs = [
            cont_source(base_cache_a.as_ptr() as *mut E4),
            cont_source(base_cache_c.as_ptr() as *mut E4),
            cont_source(base_cache_tail.as_ptr() as *mut E4),
        ];
        let metadata = GpuGKRMainLayerConstraintHostMetadata {
            quadratic_terms: vec![GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 0,
                challenge: sample_ext(31),
            }],
            linear_terms: vec![GpuGKRMainLayerConstraintLinearTerm {
                input: 0,
                challenge: sample_ext(37),
            }],
            constant_offset: E4::ZERO,
        };
        let metadata_source = GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata);
        let gate = PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
            gate_idx: 0,
            base_inputs: &base_inputs,
            ext_inputs: &[],
            batch_challenge_power_offset: 0,
            constraint_source: Some(&metadata_source),
        };
        let plan = build_flat_continuation_plan(&[gate]);
        let coeffs = resolve_plan_coeffs(
            &plan,
            sample_ext(7),
            sample_ext(3),
            sample_ext(5),
            sample_ext(9),
        );

        let base_sources = vec![vec![
            GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_a.as_ptr().cast(),
                this_layer_cache_start: base_cache_a.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_c.as_ptr().cast(),
                this_layer_cache_start: base_cache_c.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
            GpuFlatBaseAfterTwoSourceEntry {
                base_input_start: base_input_tail.as_ptr().cast(),
                this_layer_cache_start: base_cache_tail.as_ptr().cast_mut().cast(),
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
                first_access: true,
                source_kind: GpuBaseFieldSourceKind::Real,
            },
        ]];
        let ext_sources: Vec<Vec<GpuFlatContinuingSourceEntry>> = vec![vec![]];
        let desc = build_round2_desc_from_plan(&plan, &base_sources, &ext_sources);

        let first_challenge = sample_ext(301);
        let second_challenge = sample_ext(302);
        let folding_dev = alloc_and_copy(&context, &[first_challenge, second_challenge]);
        let eq_values = [sample_ext(35), sample_ext(36)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let coeffs_dev = alloc_and_copy(&context, &coeffs);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round2_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            false,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_base = vec![
            Round2BaseCpu {
                values: base_values_a,
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
            },
            Round2BaseCpu {
                values: base_values_c,
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
            },
            Round2BaseCpu {
                values: base_values_tail,
                base_layer_half_size: 8,
                base_quarter_size: 4,
                next_layer_size: 2,
            },
        ];
        let cpu_ext: Vec<ExtCpu> = vec![];
        let expected = eval_round2_cpu(
            &desc,
            &coeffs,
            &cpu_base,
            &cpu_ext,
            first_challenge,
            second_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            false,
        );

        assert_eq!(
            actual, expected,
            "flat round2 lookup-with-dens-and-setup-expressions compact mismatch"
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn flat_round3_continuation_matches_cpu() {
        let context = make_test_context(64, 8);
        let acc_size = 2usize;
        let fold_stride = acc_size;
        let next_layer_size = acc_size;

        let source0_values: Vec<E4> = (0..8).map(|i| sample_ext(700 + i)).collect();
        let source1_values: Vec<E4> = (0..8).map(|i| sample_ext(800 + i)).collect();
        let source0_dev = alloc_and_copy(&context, &source0_values);
        let source1_dev = alloc_and_copy(&context, &source1_values);
        let cache0: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let mut desc = GpuFlatContinuationStaticDesc::default();
        desc.sources[0] = GpuFlatContinuingSourceEntry {
            previous_layer_start: source0_dev.as_ptr().cast(),
            this_layer_cache_start: cache0.as_ptr().cast_mut().cast(),
        };
        desc.sources[1] = GpuFlatContinuingSourceEntry {
            previous_layer_start: source1_dev.as_ptr().cast(),
            this_layer_cache_start: cache1.as_ptr().cast_mut().cast(),
        };
        desc.num_sources = 2;
        desc.num_constants = 1;
        desc.c0_only_linear[0] = GpuFlatC0Ref { source_idx: 0 };
        desc.num_c0_only_linear = 1;
        desc.unified_quadratic[0] = GpuFlatC1Pair {
            source_a: 0,
            source_b: 1,
        };
        desc.num_unified_quadratic = 1;
        desc.unified_linear[0] = GpuFlatC0Ref { source_idx: 1 };
        desc.num_unified_linear = 1;

        let coeffs = vec![
            sample_ext(41),
            sample_ext(43),
            sample_ext(47),
            sample_ext(53),
        ];
        let coeffs_dev = alloc_and_copy(&context, &coeffs);

        let folding_challenge = sample_ext(77);
        let folding_dev = alloc_and_copy(&context, &[folding_challenge]);
        let eq_values = [sample_ext(19), sample_ext(21)];
        let eq_dev = alloc_and_copy(&context, &eq_values);
        let mut contributions: DeviceAllocation<E4> = context
            .alloc(acc_size * 2, AllocationPlacement::Top)
            .unwrap();

        launch_main_round3_flat(
            &desc,
            coeffs_dev.as_ptr(),
            folding_dev.as_ptr(),
            fold_stride as u32,
            next_layer_size as u32,
            eq_dev.as_ptr(),
            contributions.as_mut_ptr(),
            acc_size as u32,
            true,
            &context,
        )
        .unwrap();

        let actual = read_device(&context, &contributions, acc_size * 2);
        let cpu_sources = vec![
            ExtCpu {
                values: source0_values,
            },
            ExtCpu {
                values: source1_values,
            },
        ];
        let expected = eval_round3_cpu(
            &desc,
            &coeffs,
            &cpu_sources,
            folding_challenge,
            fold_stride,
            next_layer_size,
            &eq_values,
            acc_size,
            true,
        );

        assert_eq!(actual, expected, "flat round3 continuation mismatch");
    }

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
        let quad = round1_desc.unified_quadratic[0];
        assert_eq!(quad.source_a & FLAT_CONT_EXT_SOURCE_BIT, 0);
        assert_ne!(quad.source_b & FLAT_CONT_EXT_SOURCE_BIT, 0);

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
        let quad2 = round2_desc.unified_quadratic[0];
        assert_eq!(quad2.source_a & FLAT_CONT_EXT_SOURCE_BIT, 0);
        assert_ne!(quad2.source_b & FLAT_CONT_EXT_SOURCE_BIT, 0);
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
    round1_desc: Option<&GpuFlatRound1StaticDesc>,
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
