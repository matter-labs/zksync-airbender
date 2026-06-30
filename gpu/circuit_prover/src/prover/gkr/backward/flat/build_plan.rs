//! Per-gate decomposer that turns prepared gates into a flat round-0 plan
//! (source table + tier term arrays + coefficient recipes).

use super::super::super::GpuGKRStorage;
use super::super::super::GpuSumcheckRound0LaunchDescriptors;
use super::super::compact::FlatRound0BuildPlan;
use super::super::kernels::{GpuGKRMainLayerConstraintMetadataSource, GpuGKRMainLayerKernelKind};
use super::builder::FlatDescriptionBuilder;
use super::emit::{
    emit_constraint_gate, emit_cross_product_gate, emit_linear_form_times_ext,
    emit_materialize_gate, emit_single_times_linear_form,
};
use super::types::CoefficientRecipe;
use crate::primitives::field::BF;
use crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural;
use crate::upstream::Field;

pub(crate) const NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL: u32 = u32::MAX;

/// Per-gate data needed for building the flat plan.
pub(crate) struct PreparedGateForFlatPlan<'a, E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) round0: &'a GpuSumcheckRound0LaunchDescriptors<BF, E>,
    /// The power of `batch_challenge_base` assigned to this gate's first batch challenge.
    pub(crate) batch_challenge_power_offset: u32,
    /// Constraint metadata source: Immediate (test) or Deferred (production).
    pub(crate) constraint_source: Option<&'a GpuGKRMainLayerConstraintMetadataSource<E>>,
}

/// Build the flat plan from prepared gates. The returned plan carries the
/// compact `(slot, poly_idx)` source encoding directly — no separate
/// post-processing pass.
pub(crate) fn build_flat_round0_plan<'s, E: Field>(
    gates: &[PreparedGateForFlatPlan<'_, E>],
    storage: &'s GpuGKRStorage<BF, E>,
) -> FlatRound0BuildPlan<E> {
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
                // Round 0 emits only the output term (c0) + the quadratic
                // constraint gate (c2), with NO linear (c1) tier — matching the
                // CPU round-0 (step == 0 in `batch_evaluation.rs`), where
                // `evaluate_linear_term` returns early for `FIRST_ROUND` and
                // `fill_constant_term` runs only at step == 1. (A linear-tier
                // emit here over-counts the round-0 monomial.)
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
