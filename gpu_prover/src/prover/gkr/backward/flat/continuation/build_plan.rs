use super::super::super::super::GpuExtensionFieldPolyContinuingSourcePlan;
use super::super::super::kernels::{
    GpuGKRMainLayerConstraintChallengeTerm, GpuGKRMainLayerConstraintMetadataSource,
    GpuGKRMainLayerDeferredChallengeSource, GpuGKRMainLayerKernelKind,
};
use super::super::CoefficientRecipe;
use super::builder::FlatContinuationDescriptionBuilder;
use super::emit::{
    emit_continuation_constraint_gate, emit_continuation_cross_product_gate,
    emit_continuation_linear_form, emit_continuation_linear_form_times_ext,
    emit_continuation_materialize_gate, emit_continuation_single_times_linear_form,
};
use super::types::FlatContinuationBuildPlan;
use crate::primitives::field::BF;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::{Field, PrimeField};

/// Per-gate data needed for building the flat continuation plan.
pub(crate) struct PreparedGateForFlatContinuationPlan<'a, E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) gate_idx: usize,
    /// Base field inputs (as continuing sources in round 3+).
    pub(crate) base_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    /// Extension field inputs (as continuing sources).
    pub(crate) ext_inputs: &'a [GpuExtensionFieldPolyContinuingSourcePlan<E>],
    pub(crate) batch_challenge_power_offset: u32,
    pub(crate) constraint_source: Option<&'a GpuGKRMainLayerConstraintMetadataSource<E>>,
}

/// Build the flat continuation plan from prepared gates.
pub(crate) fn build_flat_continuation_plan<E: Field>(
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
