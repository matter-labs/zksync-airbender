//! Static description value types, term-type tags, and coefficient recipes
//! for the flat backward round-0 kernel. These mirror the C++ layouts in
//! `backward/flat.cuh` and feed both the builder and the kernel descriptor.

use super::super::compact::FlatRound0BuildPlan;
use super::super::kernels::GpuGKRMainLayerConstraintChallengeTerm;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;

// ---------------------------------------------------------------------------
// Constants (must match backward/flat.cuh)
// ---------------------------------------------------------------------------

// Must match backward/flat.cuh.
pub(crate) const FLAT_CONST_MAX: usize = 1024;
pub(crate) const FLAT_ROUND0_MAX_SOURCES: usize = 1280;
pub(crate) const FLAT_ROUND0_MAX_C0_BF: usize = 128;
pub(crate) const FLAT_ROUND0_MAX_C0_EXT: usize = 512;
pub(crate) const FLAT_ROUND0_MAX_C1_BF_BF: usize = 4096;
pub(crate) const FLAT_ROUND0_MAX_C1_E4_E4: usize = 512;
pub(crate) const FLAT_ROUND0_MAX_C1_BF_E4: usize = 512;
pub(crate) const FLAT_ROUND0_MAX_C1_LINEAR: usize = 128;

// ---------------------------------------------------------------------------
// Static description types (mirror CUDA structs, no field type parameter)
// ---------------------------------------------------------------------------

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuFlatC0Ref {
    pub(crate) source_idx: u16,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuFlatC1Pair {
    pub(crate) source_a: u16,
    pub(crate) source_b: u16,
}

/// Term types for the unified term array.
pub(crate) const TERM_TYPE_CONSTANT: u16 = 0;
pub(crate) const TERM_TYPE_C0_ONLY_LINEAR: u16 = 1;
pub(crate) const TERM_TYPE_UNIFIED_QUADRATIC: u16 = 2;
pub(crate) const TERM_TYPE_UNIFIED_LINEAR: u16 = 3;

/// Unified term entry: mixes all term types in a single array, sorted
/// by source-group affinity. Each term carries its type tag and an index into
/// the coefficient array so the coefficient layout doesn't need to change.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct GpuFlatUnifiedTerm {
    pub(crate) source_a: u16,
    pub(crate) source_b: u16,
    pub(crate) term_type: u16,
    pub(crate) coeff_idx: u16,
}

// ---------------------------------------------------------------------------
// Coefficient recipes
// ---------------------------------------------------------------------------

/// Describes how to compute a single term's coefficient at runtime.
///
/// The coefficient is: `base^batch_power * immediate_recipe * Π(prefactor_i)`,
/// negated if `negate` is true.
///
/// - `immediate_recipe`: structural build-time factor (constraint coefficient, sign, etc.)
/// - `prefactors`: each evaluated at runtime via `evaluate_constraint_prefactor`
#[derive(Clone)]
pub(crate) struct CoefficientRecipe {
    pub(crate) batch_power: u32,
    pub(crate) negate: bool,
    pub(crate) immediate_recipe: ImmediateFactorRecipeStructural,
    /// 0..2 additional challenge prefactors evaluated at runtime.
    pub(crate) prefactors: Vec<Vec<GpuGKRMainLayerConstraintChallengeTerm>>,
}

pub(crate) fn immediate_recipe_with_negation(
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

impl FlatRound0BuildPlan {
    pub(crate) fn total_coefficients(&self) -> usize {
        self.recipes.len()
    }
}
