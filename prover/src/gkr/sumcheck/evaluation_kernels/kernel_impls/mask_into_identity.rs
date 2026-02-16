use super::*;

#[derive(Debug)]
pub struct MaskIntoIdentityProductGKRRelation {
    pub input: GKRAddress,
    pub mask: GKRAddress,
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for MaskIntoIdentityProductGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: vec![self.mask],
            inputs_in_extension: vec![self.input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![self.output],
        }
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = MaskIntoIdentityProductGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        forward_evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs(
            &kernel,
            &inputs,
            storage,
            expected_output_layer,
            trace_len,
            worker,
        );
    }

    fn evaluate_over_storage<const N: usize>(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        batch_challenges: &[E],
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
        worker: &Worker,
    ) {
        assert_eq!(
            batch_challenges.len(),
            <Self as BatchedGKRKernel<F, E>>::num_challenges(self)
        );
        let kernel = MaskIntoIdentityProductGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs(
            &kernel,
            &inputs,
            storage,
            step,
            batch_challenges,
            folding_challenges,
            accumulator,
            total_sumcheck_rounds,
            last_evaluations,
            worker,
        );
    }
}

#[derive(Default)]
pub struct MaskIntoIdentityProductGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 1, 1, 1>
    for MaskIntoIdentityProductGKRRelationKernel<F, E>
{
    // The quadratic coefficient is La * Lm, NOT kernel([La, Lm]) which would include (1 - Lm).
    fn evaluate_first_round<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; 1],
        ext_sources: &[SE; 1],
        output_sources: &[SOUT; 1],
        batch_challenges: &[E; 1],
    ) -> [E; 2] {
        // constant term comes from output.f0 (like the default implementation)
        let output_f0 = output_sources[0].get_f0_only(index).into_value();
        let mut eval_c0 = batch_challenges[0];
        eval_c0.mul_assign(&output_f0);

        // quadratic coefficient = La * Lm (product of slopes)
        let input_slope = ext_sources[0].get_f1_minus_f0_only(index).into_value();
        let mask_slope = sources[0].get_f1_minus_f0_only(index).0;

        let mut c2 = input_slope;
        c2.mul_assign_by_base(&mask_slope);

        let mut eval_c2 = batch_challenges[0];
        eval_c2.mul_assign(&c2);

        [eval_c0, eval_c2]
    }

    // Override evaluate because this kernel has an affine term (1 - mask).
    // The sumcheck polynomial s(X) = input(X) * mask(X) + (1 - mask(X))
    // Let input(X) = a0 + La*X, mask(X) = m0 + Lm*X
    // Then s(X) = (a0*m0 + 1 - m0) + (a0*Lm + La*m0 - Lm)*X + La*Lm*X²
    //
    // The quadratic coefficient is La*Lm, NOT kernel([La, Lm]) which would incorrectly
    // include the (1 - Lm) affine term.

    fn evaluate<
        RB: EvaluationRepresentation<F, E>,
        SB: EvaluationFormStorage<F, E, RB>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[SB; 1],
        ext_sources: &[SE; 1],
        batch_challenges: &[E; 1],
    ) -> [E; 2] {
        let ctx = sources[0].get_collapse_context();
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            let [input_f0, input_f1] = ext_sources[0].get_two_points::<true>(index);
            let [mask_f0, mask_f1] = sources[0].get_two_points::<true>(index);

            // kernel(a, m) = a * m + (1 - m)
            let k0 = mask_f0.mul_by_ext::<true>(&input_f0.value, ctx);
            let mut k0 = mask_f0.sub_from_ext::<true>(&k0, ctx);
            k0.add_assign_base(&F::ONE);
            k0.mul_assign(&batch_challenges[0]);

            let k1 = mask_f1.mul_by_ext::<true>(&input_f1.value, ctx);
            let mut k1 = mask_f1.sub_from_ext::<true>(&k1, ctx);
            k1.add_assign_base(&F::ONE);
            k1.mul_assign(&batch_challenges[0]);

            [k0, k1]
        } else {
            // For non-explicit form, return [constant_term, quadratic_coeff]
            // constant_term = kernel(input.f0, mask.f0) = input.f0 * mask.f0 + (1 - mask.f0)
            // quadratic_coeff = La * Lm = (input.f1 - input.f0) * (mask.f1 - mask.f0)
            let [input_f0, input_slope] = ext_sources[0].get_two_points::<false>(index);
            let [mask_f0, mask_slope] = sources[0].get_two_points::<false>(index);

            // constant_term = input.f0 * mask.f0 + (1 - mask.f0)
            let k0 = mask_f0.mul_by_ext::<true>(&input_f0.value, ctx);
            let mut k0 = mask_f0.sub_from_ext::<true>(&k0, ctx);
            k0.add_assign_base(&F::ONE);
            k0.mul_assign(&batch_challenges[0]);

            // quadratic_coeff = La * Lm (just the product of slopes, no affine term!)
            let mut c2 = mask_slope.mul_by_ext::<true>(&input_slope.value, ctx);
            c2.mul_assign(&batch_challenges[0]);

            [k0, c2]
        }
    }

    // #[inline(always)]
    // fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; 2]) -> [E; 1] {
    //     let [val, mask] = input;
    //     let val = val.into_value();
    //     let mask = mask.into_value();
    //     // input * mask + (1 - mask)
    //     let mut result = val;
    //     result.mul_assign(&mask);
    //     let mut one_minus_mask = E::ONE;
    //     one_minus_mask.sub_assign(&mask);
    //     result.add_assign(&one_minus_mask);
    //     [result]
    // }

    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: &[RB; 1],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
        _ctx: &RB::CollapseContext,
    ) -> [E; 1] {
        unreachable!("unused for this kernel");
    }

    #[inline(always)]
    fn pointwise_eval_forward(
        &self,
        input: &[BaseFieldRepresentation<F>; 1],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
    ) -> [E; 1] {
        let [mask] = input;
        let [value] = ext_input;
        if mask.0.as_boolean() {
            [value.into_value()]
        } else {
            [E::ONE]
        }
    }
}
