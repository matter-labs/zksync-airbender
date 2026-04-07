use cs::definitions::GKRAddress;
use worker::Worker;

use crate::definitions::sumcheck_kernel::fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupBaseMinusMultiplicityByBaseGKRRelation<F: PrimeField, E: FieldExtension<F> + Field>
{
    pub input: GKRAddress,
    pub setup: [GKRAddress; 2],
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: vec![self.input, self.setup[0], self.setup[1]],
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: self.outputs.to_vec(),
        }
    }

    fn terms(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
        let [c, d] = self.setup;
        let b = self.input;

        let b = (
            BTreeMap::from_iter([(b, E::ONE)]),
            challenge_constants.lookup_challenges_additive_part,
        );
        let d = (
            BTreeMap::from_iter([(d, E::ONE)]),
            challenge_constants.lookup_challenges_additive_part,
        );
        let c = (BTreeMap::from_iter([(c, E::MINUS_ONE)]), E::ZERO);

        let mut num_term = BatchedGKRTermDescription::default();
        num_term.add_linear_base_terms(d.clone());
        num_term.add_product_of_linear_base_terms(c, b.clone());
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = BatchedGKRTermDescription::default();
        den_term.add_product_of_linear_base_terms(b, d);
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = LookupBaseMinusMultiplicityByBaseGKRRelationKernel::<F, E>::new(
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
        let kernel = LookupBaseMinusMultiplicityByBaseGKRRelationKernel::<F, E>::new(
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
pub struct LookupBaseMinusMultiplicityByBaseGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    LookupBaseMinusMultiplicityByBaseGKRRelationKernel<F, E>
{
    pub(crate) fn new(lookup_additive_challenge: E) -> Self {
        Self {
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernelCore<F, E, 3, 0, 2>
    for LookupBaseMinusMultiplicityByBaseGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 3],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 0],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        pointwise_eval_impl(input, ctx, &self.lookup_additive_challenge)
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 3],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 0],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        pointwise_eval_quadratic_only_impl(input, ctx)
    }

    fn pointwise_eval_by_ref<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: [&RB; 3],
        _ext_input: [&ExtensionFieldRepresentation<F, E>; 0],
        _ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 3, 0, 2>
    for LookupBaseMinusMultiplicityByBaseGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; 3],
        _ext_sources: &[SE; 0],
        output_sources: &[SOUT; 2],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        let [b1, c1, d1] = if SB::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            let [_b0, b1] = sources[0].get_two_points::<false>(index);
            let [_c0, c1] = sources[1].get_two_points::<false>(index);
            let [_d0, d1] = sources[2].get_two_points::<false>(index);

            [b1, c1, d1]
        } else {
            let b1 = sources[0].get_f1_minus_f0_only(index);
            let c1 = sources[1].get_f1_minus_f0_only(index);
            let d1 = sources[2].get_f1_minus_f0_only(index);

            [b1, c1, d1]
        };

        let [mut eval_0_term_0, mut eval_0_term_1] = output_sources
            .each_ref()
            .map(|el| el.get_f0_only(index).into_value());
        let [mut eval_1_term_0, mut eval_1_term_1] =
            pointwise_eval_quadratic_only_impl::<F, E, _>(&[b1, c1, d1], &());

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
        sources: &[SB; 3],
        _ext_sources: &[SE; 0],
        batch_challenges: &[E; 2],
    ) -> [E; 2] {
        // 1/b - c/d -> (d - c*b), bd
        let ctx = sources[0].get_collapse_context();
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            let [b0, b1] = sources[0].get_two_points::<true>(index);
            let [c0, c1] = sources[1].get_two_points::<true>(index);
            let [d0, d1] = sources[2].get_two_points::<true>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[b0, c0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_impl(&[b1, c1, d1], ctx, &self.lookup_additive_challenge);

            eval_0_term_0.mul_assign(&batch_challenges[0]);
            eval_0_term_1.mul_assign(&batch_challenges[1]);

            eval_1_term_0.mul_assign(&batch_challenges[0]);
            eval_1_term_1.mul_assign(&batch_challenges[1]);

            eval_0_term_0.add_assign(&eval_0_term_1);
            eval_1_term_0.add_assign(&eval_1_term_1);

            [eval_0_term_0, eval_1_term_0]
        } else {
            let [b0, b1] = sources[0].get_two_points::<false>(index);
            let [c0, c1] = sources[1].get_two_points::<false>(index);
            let [d0, d1] = sources[2].get_two_points::<false>(index);
            let [mut eval_0_term_0, mut eval_0_term_1] =
                pointwise_eval_impl(&[b0, c0, d0], ctx, &self.lookup_additive_challenge);
            let [mut eval_1_term_0, mut eval_1_term_1] =
                pointwise_eval_quadratic_only_impl(&[b1, c1, d1], ctx);

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
    input: &[RB; 3],
    ctx: &RB::CollapseContext,
    lookup_additive_challenge: &E,
) -> [E; 2] {
    // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
    let [b, c, d] = input;
    let b = b.add_with_ext::<true>(lookup_additive_challenge, ctx);
    let d = d.add_with_ext::<true>(lookup_additive_challenge, ctx);
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
    input: &[RB; 3],
    ctx: &RB::CollapseContext,
) -> [E; 2] {
    // only quadratic terms for: 1/(b + gamma) - c/(d + gamma) -> (-c * b), (b * d)
    let [b, c, d] = input;
    let b_ext = b.mul_by_ext::<true>(&E::ONE, ctx);
    let mut num = c.mul_by_ext::<true>(&b_ext, ctx);
    num.negate();
    let den = d.mul_by_ext::<true>(&b_ext, ctx);

    [num, den]
}
