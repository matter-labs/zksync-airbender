//! Compile host-side `CoefficientRecipe<E>` entries into the device-side
//! `GpuFlatRecipeEvalDesc` layout consumed by `evaluate_constraint_prefactor`.

use super::super::kernels::GpuGKRMainLayerDeferredChallengeSource;
use super::types::CoefficientRecipe;
use crate::primitives::field::BF;
use crate::prover::gkr::eval_recipes::{
    GpuFlatRecipeEvalDesc, GpuPrefactorTerm, GpuRecipeHeader, RecipeEvalHostArrays,
    FLAT_IMMEDIATE_MAX_MONOMIALS, FLAT_IMMEDIATE_MAX_RECIPES, FLAT_RECIPE_MAX_HEADERS,
    FLAT_RECIPE_MAX_TERMS,
};
use crate::prover::gkr::immediate_factors::ImmediateFactorInterner;
use crate::upstream::Field;

/// Compiled recipe buffer ready for device upload.
///
/// Dual-path (Stage 3c): when every table fits its inline cap, `desc` is a
/// populated inline `GpuFlatRecipeEvalDesc` and `device_arrays` is `None`
/// (the fast, byte-identical path passed by value as a `__grid_constant__`
/// kernel arg). When any table overflows its cap (e.g. bigint's 3006 recipes
/// vs the 2816-header cap), `desc` is left default-zero (unused) and
/// `device_arrays` carries the host arrays for H2D upload into device buffers
/// read by the `_devptr` eval-recipes kernels.
#[allow(dead_code)]
pub(crate) struct CompiledRecipeBuffers {
    pub(crate) desc: Box<GpuFlatRecipeEvalDesc>,
    pub(crate) num_recipes: usize,
    pub(crate) num_terms: usize,
    pub(crate) num_immediate_recipes: usize,
    pub(crate) num_immediate_monomials: usize,
    /// `Some` iff any table overflows its inline cap → device-pointer path.
    pub(crate) device_arrays: Option<RecipeEvalHostArrays>,
}

/// Compile `CoefficientRecipe` entries into the device-side format.
pub(crate) fn compile_recipes_for_device<E: Field + field::FieldExtension<BF>>(
    recipes: &[CoefficientRecipe<E>],
) -> CompiledRecipeBuffers {
    // Build the four tables as plain `Vec`s first. Whether they land in an
    // inline `__grid_constant__` descriptor or in device buffers is decided
    // afterwards from their sizes (Stage 3c dual path); the values are identical
    // either way. The `terms_offset`/`immediate_idx` header fields are `u16`, so
    // those bounds are enforced regardless of path (they cap the device form too).
    let mut headers: Vec<GpuRecipeHeader> = Vec::with_capacity(recipes.len());
    let mut terms: Vec<GpuPrefactorTerm> = Vec::new();
    let mut immediate_interner = ImmediateFactorInterner::new();

    for recipe in recipes.iter() {
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

        let immediate_recipe = if recipe.negate {
            recipe.immediate_recipe.negated()
        } else {
            recipe.immediate_recipe.clone()
        };
        let immediate_idx = immediate_interner.intern(immediate_recipe);

        headers.push(GpuRecipeHeader {
            batch_power: recipe.batch_power as u16,
            group_count_0: group_counts[0],
            group_count_1: group_counts[1],
            terms_offset: terms_offset as u16,
            immediate_idx,
        });
    }

    let (immediate_headers, immediate_monomials) = immediate_interner.materialize();

    let num_recipes = headers.len();
    let num_terms = terms.len();
    let num_immediate_recipes = immediate_headers.len();
    let num_immediate_monomials = immediate_monomials.len();

    // Any table exceeding its inline cap forces the device-pointer path for the
    // whole descriptor. Individual per-table caps are what keep the inline
    // `GpuFlatRecipeEvalDesc` under the 32 KB kernel-arg ceiling, so checking
    // them individually is sufficient.
    let use_device = num_recipes > FLAT_RECIPE_MAX_HEADERS
        || num_terms > FLAT_RECIPE_MAX_TERMS
        || num_immediate_recipes > FLAT_IMMEDIATE_MAX_RECIPES
        || num_immediate_monomials > FLAT_IMMEDIATE_MAX_MONOMIALS;

    let (desc, device_arrays) = if use_device {
        // Device path: retain the host arrays for H2D upload; leave the inline
        // descriptor default-zero (unused — the `_devptr` kernels ignore it).
        (
            Box::<GpuFlatRecipeEvalDesc>::default(),
            Some(RecipeEvalHostArrays {
                headers,
                terms,
                immediate_recipes: immediate_headers,
                immediate_monomials,
            }),
        )
    } else {
        // Inline path: copy each table into the fixed-size descriptor arrays.
        // Byte-identical to the pre-Stage-3c behaviour.
        let mut desc = Box::<GpuFlatRecipeEvalDesc>::default();
        desc.headers[..num_recipes].copy_from_slice(&headers);
        desc.terms[..num_terms].copy_from_slice(&terms);
        desc.immediate_recipes[..num_immediate_recipes].copy_from_slice(&immediate_headers);
        desc.immediate_monomials[..num_immediate_monomials].copy_from_slice(&immediate_monomials);
        (desc, None)
    };

    CompiledRecipeBuffers {
        desc,
        num_recipes,
        num_terms,
        num_immediate_recipes,
        num_immediate_monomials,
        device_arrays,
    }
}
