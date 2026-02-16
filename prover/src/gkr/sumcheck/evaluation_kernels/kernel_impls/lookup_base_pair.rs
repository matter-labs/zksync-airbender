use cs::definitions::GKRAddress;
use worker::Worker;

use super::*;

#[derive(Debug)]
pub struct LookupBasePairGKRRelation<F: PrimeField, E: FieldExtension<F> + Field> {
    pub inputs: [GKRAddress; 2],
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupBasePairGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: self.inputs.to_vec(),
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: self.outputs.to_vec(),
        }
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = LookupBasePairGKRRelationKernel::<F, E> {
            lookup_additive_challenge: self.lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
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
        let kernel = LookupBasePairGKRRelationKernel::<F, E> {
            lookup_additive_challenge: self.lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
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

// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct LookupBasePairGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 2, 0, 2>
    for LookupBasePairGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; 2],
        _ext_sources: &[SE; 0],
        output_sources: &[SOUT; 2],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        // 1/b + 1/d -> (b + d), bd
        let [b1, d1] = if SB::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            let [_b0, b1] = sources[0].get_two_points::<false>(index);
            let [_d0, d1] = sources[1].get_two_points::<false>(index);

            [b1, d1]
        } else {
            let b1 = sources[0].get_f1_minus_f0_only(index);
            let d1 = sources[1].get_f1_minus_f0_only(index);

            [b1, d1]
        };

        let [mut eval_0_term_0, mut eval_0_term_1] = output_sources
            .each_ref()
            .map(|el| el.get_f0_only(index).into_value());
        let [mut eval_1_term_0, mut eval_1_term_1]: [E; 2] =
            pointwise_eval_quadratic_only_impl(&[b1, d1], &());

        eval_0_term_0.mul_assign(&batch_challenges[0]);
        eval_0_term_1.mul_assign(&batch_challenges[1]);

        eval_1_term_0.mul_assign(&batch_challenges[0]);
        eval_1_term_1.mul_assign(&batch_challenges[1]);

        eval_0_term_0.add_assign(&eval_0_term_1);
        eval_1_term_0.add_assign(&eval_1_term_1);

        [eval_0_term_0, eval_1_term_0]
    }

    #[inline(always)]
    fn evaluate<
        RB: EvaluationRepresentation<F, E>,
        SB: EvaluationFormStorage<F, E, RB>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[SB; 2],
        _ext_sources: &[SE; 0],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        let ctx = sources[0].get_collapse_context();
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            let [b0, b1] = sources[0].get_two_points::<true>(index);
            let [d0, d1] = sources[1].get_two_points::<true>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[b0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_impl(&[b1, d1], ctx, &self.lookup_additive_challenge);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        } else {
            let [b0, b1] = sources[0].get_two_points::<false>(index);
            let [d0, d1] = sources[1].get_two_points::<false>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[b0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_quadratic_only_impl(&[b1, d1], ctx);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        }
    }

    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: &[RB; 2],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 0],
        _ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        unreachable!("unused by this kernel");
    }

    #[inline(always)]
    fn pointwise_eval_forward(
        &self,
        input: &[BaseFieldRepresentation<F>; 2],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 0],
    ) -> [E; 2] {
        pointwise_eval_impl(input, &(), &self.lookup_additive_challenge)
    }
}

#[inline(always)]
fn pointwise_eval_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 2],
    ctx: &RB::CollapseContext,
    lookup_additive_challenge: &E,
) -> [E; 2] {
    // 1/b + 1/d -> (b + d), bd
    let [b, d] = input;
    let b = b.add_with_ext::<true>(lookup_additive_challenge, ctx);
    let d = d.add_with_ext::<true>(lookup_additive_challenge, ctx);
    let mut num = b;
    num.add_assign(&d);

    let mut den = b;
    den.mul_assign(&d);

    [num, den]
}

#[inline(always)]
fn pointwise_eval_quadratic_only_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 2],
    ctx: &RB::CollapseContext,
) -> [E; 2] {
    // 1/b + 1/d -> zero, bd
    let [b, d] = input;
    let d_ext = d.mul_by_ext::<true>(&E::ONE, ctx);
    let den = b.mul_by_ext::<true>(&d_ext, ctx);

    [E::ZERO, den]
}
