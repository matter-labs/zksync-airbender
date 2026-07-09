use super::super::kernels::GpuGKRMainLayerConstraintMetadataSource;
use super::continuation::build_plan::PreparedGateForFlatContinuationPlan;
use super::continuation::builder::FlatContinuationDescriptionBuilder;
use super::{
    immediate_recipe_with_negation, CoefficientRecipe, NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL,
};
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::Field;

/// Emit terms for constraint gates in continuation rounds.
/// Quadratic constraint terms → unified_quadratic (always both c0 and c1).
/// Linear constraint terms → c0_only_linear (compact: c0 only; explicit: both).
/// Constant offset → constant term.
pub(super) fn emit_continuation_constraint_gate<E: Field>(
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
pub(super) fn emit_continuation_cross_product_gate<E: Field>(
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
pub(super) fn emit_continuation_materialize_gate<E: Field>(
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
        }
        None => panic!("materialize gate requires metadata"),
    }
}

/// Emit unified_quadratic: cached_src × linear_form_term for each term.
/// When `use_linear_terms` is true, iterates `linear_terms`; otherwise `quadratic_terms` (using lhs).
pub(super) fn emit_continuation_single_times_linear_form<E: Field>(
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
pub(super) fn emit_continuation_linear_form<E: Field>(
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
pub(super) fn emit_continuation_linear_form_times_ext<E: Field>(
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
