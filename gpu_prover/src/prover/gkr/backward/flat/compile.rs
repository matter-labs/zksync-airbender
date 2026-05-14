//! Compile host-side `CoefficientRecipe<E>` entries into the device-side
//! `GpuFlatRecipeEvalDesc` layout consumed by `evaluate_constraint_prefactor`.

use super::super::kernels::GpuGKRMainLayerDeferredChallengeSource;
use super::types::CoefficientRecipe;
use crate::primitives::field::BF;
use crate::prover::gkr::eval_recipes::{
    GpuFlatRecipeEvalDesc, GpuPrefactorTerm, GpuRecipeHeader, FLAT_IMMEDIATE_MAX_MONOMIALS,
    FLAT_IMMEDIATE_MAX_RECIPES, FLAT_RECIPE_MAX_HEADERS, FLAT_RECIPE_MAX_TERMS,
};
use crate::prover::gkr::immediate_factors::ImmediateFactorInterner;
use crate::upstream::Field;

/// Compiled recipe buffer ready for device upload.
#[allow(dead_code)]
pub(crate) struct CompiledRecipeBuffers {
    pub(crate) desc: Box<GpuFlatRecipeEvalDesc>,
    pub(crate) num_recipes: usize,
    pub(crate) num_terms: usize,
    pub(crate) num_immediate_recipes: usize,
    pub(crate) num_immediate_monomials: usize,
}

/// Compile `CoefficientRecipe` entries into the device-side format.
pub(crate) fn compile_recipes_for_device<E: Field + field::FieldExtension<BF>>(
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
