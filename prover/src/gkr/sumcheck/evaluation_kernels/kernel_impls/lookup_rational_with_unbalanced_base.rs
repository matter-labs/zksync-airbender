use cs::definitions::GKRAddress;
use worker::Worker;

use crate::definitions::sumcheck_kernel::fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupRationalPairWithUnbalancedBaseGKRRelation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub inputs: [GKRAddress; 2],
    pub remainder: GKRAddress,
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupRationalPairWithUnbalancedBaseGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: vec![self.remainder],
            inputs_in_extension: self.inputs.to_vec(),
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
        let kernel = LookupRationalPairWithUnbalancedBaseGKRRelationKernel::<F, E> {
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
        let kernel = LookupRationalPairWithUnbalancedBaseGKRRelationKernel::<F, E> {
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
pub struct LookupRationalPairWithUnbalancedBaseGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernelCore<F, E, 1, 2, 2>
    for LookupRationalPairWithUnbalancedBaseGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 1],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        pointwise_eval_impl(input, ext_input, ctx, &self.lookup_additive_challenge)
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 1],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        pointwise_eval_quadratic_only_impl(input, ext_input, ctx)
    }

    fn pointwise_eval_by_ref<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: [&RB; 1],
        _ext_input: [&ExtensionFieldRepresentation<F, E>; 2],
        _ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 1, 2, 2>
    for LookupRationalPairWithUnbalancedBaseGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; 1],
        ext_sources: &[SE; 2],
        output_sources: &[SOUT; 2],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        // a/b + 1/d -> (ad + b), bd
        let (a1, b1, d1) = if SB::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            let [_a0, a1] = ext_sources[0].get_two_points::<false>(index);
            let [_b0, b1] = ext_sources[1].get_two_points::<false>(index);
            let [_d0, d1] = sources[0].get_two_points::<false>(index);

            (a1, b1, d1)
        } else {
            let a1 = ext_sources[0].get_f1_minus_f0_only(index);
            let b1 = ext_sources[1].get_f1_minus_f0_only(index);
            let d1 = sources[0].get_f1_minus_f0_only(index);

            (a1, b1, d1)
        };

        let [mut eval_0_term_0, mut eval_0_term_1] = output_sources
            .each_ref()
            .map(|el| el.get_f0_only(index).into_value());
        let [mut eval_1_term_0, mut eval_1_term_1] =
            pointwise_eval_quadratic_only_impl(&[d1], &[a1, b1], &());

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
        sources: &[SB; 1],
        ext_sources: &[SE; 2],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        let ctx = sources[0].get_collapse_context();
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            let [a0, a1] = ext_sources[0].get_two_points::<true>(index);
            let [b0, b1] = ext_sources[1].get_two_points::<true>(index);
            let [d0, d1] = sources[0].get_two_points::<true>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[d0], &[a0, b0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_impl(&[d1], &[a1, b1], ctx, &self.lookup_additive_challenge);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        } else {
            let [a0, a1] = ext_sources[0].get_two_points::<false>(index);
            let [b0, b1] = ext_sources[1].get_two_points::<false>(index);
            let [d0, d1] = sources[0].get_two_points::<false>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[d0], &[a0, b0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_quadratic_only_impl(&[d1], &[a1, b1], ctx);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        }
    }
}

#[inline(always)]
fn pointwise_eval_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 1],
    ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
    ctx: &RB::CollapseContext,
    lookup_additive_challenge: &E,
) -> [E; 2] {
    // a/b + 1/d -> (ad + b), bd
    let [d] = input;
    let [a, b] = ext_input;
    let d = d.add_with_ext::<true>(lookup_additive_challenge, ctx);
    let mut num = a.value;
    num.mul_assign(&d);
    num.add_assign(&b.value);

    let mut den = b.into_value();
    den.mul_assign(&d);

    [num, den]
}

#[inline(always)]
fn pointwise_eval_quadratic_only_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 1],
    ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
    ctx: &RB::CollapseContext,
) -> [E; 2] {
    // a/b + 1/(d+constant) -> (ad), bd
    let [d] = input;
    let [a, b] = ext_input;
    let num = d.mul_by_ext::<true>(&a.value, ctx);
    let den = d.mul_by_ext::<true>(&b.value, ctx);

    [num, den]
}
