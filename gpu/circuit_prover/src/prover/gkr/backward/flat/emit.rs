//! Constraint-gate decomposition helpers used by `build_flat_round0_plan` to
//! emit per-term coefficient recipes for gates that carry constraint
//! metadata (linear-form / quadratic / materialize / cross-product gates).

use super::super::super::GpuSumcheckRound0LaunchDescriptors;
use super::super::kernels::{
    GpuGKRMainLayerConstraintMetadataSource, GpuGKRMainLayerConstraintTemplate,
};
use super::build_plan::{PreparedGateForFlatPlan, NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL};
use super::builder::FlatDescriptionBuilder;
use super::types::CoefficientRecipe;
use crate::primitives::field::BF;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::Field;

/// Emit c1 terms for gates that use quadratic constraint metadata directly.
/// c1 += β * Σ (constraint_quad[i].challenge * Δ(lhs) * Δ(rhs))
pub(super) fn emit_constraint_gate<E: Field>(
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
pub(super) fn emit_cross_product_gate<E: Field>(
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
pub(super) fn emit_materialize_gate<E: Field>(
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
pub(super) fn emit_single_times_linear_form<E: Field>(
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
pub(super) fn emit_linear_form_times_ext<E: Field>(
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
