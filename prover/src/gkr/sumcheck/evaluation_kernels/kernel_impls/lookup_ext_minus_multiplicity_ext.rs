use cs::definitions::GKRAddress;
use worker::Worker;

use crate::definitions::sumcheck_kernel::fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupExtensionMinusMultiplicityByExtensionGKRRelation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub input: GKRAddress,
    pub setup: [GKRAddress; 2],
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupExtensionMinusMultiplicityByExtensionGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: vec![self.setup[0]],
            inputs_in_extension: vec![self.input, self.setup[1]],
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
        let kernel = LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel::<F, E>::new(
            self.lookup_additive_challenge,
        );
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
        let kernel = LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel::<F, E>::new(
            self.lookup_additive_challenge,
        );
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
pub struct LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel<F, E>
{
    pub(crate) fn new(lookup_additive_challenge: E) -> Self {
        Self {
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernelCore<F, E, 1, 2, 2>
    for LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel<F, E>
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
    for LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel<F, E>
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
        let ([c1], [b1, d1]) = if SB::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            let [_c0, c1] = sources[0].get_two_points::<false>(index);
            let [_b0, b1] = ext_sources[0].get_two_points::<false>(index);
            let [_d0, d1] = ext_sources[1].get_two_points::<false>(index);

            ([c1], [b1, d1])
        } else {
            let c1 = sources[0].get_f1_minus_f0_only(index);
            let b1 = ext_sources[0].get_f1_minus_f0_only(index);
            let d1 = ext_sources[1].get_f1_minus_f0_only(index);

            ([c1], [b1, d1])
        };

        let [mut eval_0_term_0, mut eval_0_term_1] = output_sources
            .each_ref()
            .map(|el| el.get_f0_only(index).into_value());
        let [mut eval_1_term_0, mut eval_1_term_1] =
            pointwise_eval_quadratic_only_impl(&[c1], &[b1, d1], &());

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
        // 1/b - c/d -> (d - c*b), bd
        let ctx = sources[0].get_collapse_context();
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            let [c0, c1] = sources[0].get_two_points::<true>(index);
            let [b0, b1] = ext_sources[0].get_two_points::<true>(index);
            let [d0, d1] = ext_sources[1].get_two_points::<true>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[c0], &[b0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_impl(&[c1], &[b1, d1], ctx, &self.lookup_additive_challenge);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        } else {
            let [c0, c1] = sources[0].get_two_points::<false>(index);
            let [b0, b1] = ext_sources[0].get_two_points::<false>(index);
            let [d0, d1] = ext_sources[1].get_two_points::<false>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[c0], &[b0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_quadratic_only_impl(&[c1], &[b1, d1], ctx);

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
    // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
    let [c] = input;
    let [b, d] = ext_input;

    let b = b.add_with_ext::<true>(lookup_additive_challenge, &());
    let d = d.add_with_ext::<true>(lookup_additive_challenge, &());
    let cb = c.mul_by_ext::<true>(&b, ctx);
    let mut num = d;
    num.sub_assign(&cb);

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
    input: &[RB; 1],
    ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
    ctx: &RB::CollapseContext,
) -> [E; 2] {
    // only quadratic terms for: 1/(b + gamma) - c/(d + gamma) -> (-c * b), (b * d)
    let [c] = input;
    let [b, d] = ext_input;

    let b_ext = b.into_value();
    let mut num = c.mul_by_ext::<true>(&b_ext, ctx);
    num.negate();
    let den = d.mul_by_ext::<true>(&b_ext, &());

    [num, den]
}
