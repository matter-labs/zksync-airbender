use crate::definitions::sumcheck_kernel::{
    fixed_over_base::BaseFieldInOutFixedSizesEvaluationKernelCore,
    fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore,
};

use super::*;

#[derive(Debug)]
pub struct BaseFieldCopyGKRRelation {
    pub input: GKRAddress,
    pub output: GKRAddress,
}

impl BaseFieldCopyGKRRelation {
    #[inline]
    fn validate(&self) -> bool {
        !self.output.is_cache()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for BaseFieldCopyGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        assert!(self.validate());
        GKRInputs {
            inputs_in_base: vec![self.input],
            inputs_in_extension: Vec::new(),
            outputs_in_base: vec![self.output],
            outputs_in_extension: Vec::new(),
        }
    }

    fn terms(
        &self,
        _challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let mut term = BatchedGKRTermDescription::default();
        term.add_linear_with_base(self.input, E::ONE);
        term.set_base_output(self.output);
        vec![term]
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = ExtensionCopyGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        forward_evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs(
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
        let kernel = BaseFieldCopyGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        evaluate_single_input_type_fixed_in_out_kernel_with_base_inputs(
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
pub struct BaseFieldCopyGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    BaseFieldInOutFixedSizesEvaluationKernelCore<F, E, 1, 1>
    for BaseFieldCopyGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<R: EvaluationRepresentation<F, E>>(&self, input: &[R; 1]) -> [R; 1] {
        *input
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only<R: EvaluationRepresentation<F, E>>(
        &self,
        _input: &[R; 1],
    ) -> [R; 1] {
        unreachable!("not used by this kernel")
    }

    #[inline(always)]
    fn pointwise_eval_forward(&self, _input: &[BaseFieldRepresentation<F>; 1]) -> [F; 1] {
        unreachable!("not used by this kernel")
    }

    #[inline(always)]
    fn pointwise_eval_by_ref<R: EvaluationRepresentation<F, E>>(&self, input: [&R; 1]) -> [R; 1] {
        input.map(|el| *el)
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    BaseFieldInOutFixedSizesEvaluationKernel<F, E, 1, 1> for BaseFieldCopyGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        S: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SOUT: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
    >(
        &self,
        index: usize,
        _sources: &[S; 1],
        output_sources: &[SOUT; 1],
        batch_challenges: &[E; 1],
    ) -> [E; 2] {
        let output_f0 = output_sources[0]
            .get_f0_only(index)
            .collapse_into_ext_with_challenge(&(), &batch_challenges[0]);

        // result[1] = 0 because the quadratic coefficient is 0 for a linear function
        [output_f0, E::ZERO]
    }

    #[inline(always)]
    fn evaluate<
        R: EvaluationRepresentation<F, E>,
        S: EvaluationFormStorage<F, E, R>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[S; 1],
        batch_challenges: &[E; 1],
        collapse_ctx: &R::CollapseContext,
    ) -> [E; 2] {
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            // For Copy, kernel is identity, so this is just [f0, f1]
            let [f0, f1] = sources[0].get_two_points::<true>(index);
            let f0_val = f0.collapse_into_ext_with_challenge(collapse_ctx, &batch_challenges[0]);
            let f1_val = f1.collapse_into_ext_with_challenge(collapse_ctx, &batch_challenges[0]);
            [f0_val, f1_val]
        } else {
            // For non-explicit form (intermediate rounds), return [f0, 0]
            // The quadratic coefficient is 0 for a linear function
            if S::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
                let [f0, _] = sources[0].get_two_points::<EXPLICIT_FORM>(index);

                let f0 = f0.collapse_into_ext_with_challenge(collapse_ctx, &batch_challenges[0]);
                [f0, E::ZERO]
            } else {
                let f0 = sources[0]
                    .get_f0_only(index)
                    .collapse_into_ext_with_challenge(collapse_ctx, &batch_challenges[0]);
                [f0, E::ZERO]
            }
        }
    }
}

#[derive(Debug)]
pub struct ExtensionCopyGKRRelation {
    pub input: GKRAddress,
    pub output: GKRAddress,
}

impl ExtensionCopyGKRRelation {
    #[inline]
    fn validate(&self) -> bool {
        !self.output.is_cache()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for ExtensionCopyGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        assert!(self.validate());
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![self.input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![self.output],
        }
    }

    fn terms(
        &self,
        _challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let mut term = BatchedGKRTermDescription::default();
        term.add_linear_with_ext(self.input, E::ONE);
        term.set_extension_output(self.output);
        vec![term]
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = ExtensionCopyGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        forward_evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs(
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
        let kernel = ExtensionCopyGKRRelationKernel::default();
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs(
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

#[derive(Default, Debug)]
pub struct ExtensionCopyGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernelCore<F, E, 1, 1>
    for ExtensionCopyGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; 1]) -> [E; 1] {
        [input[0].into_value()]
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only(
        &self,
        _input: &[ExtensionFieldRepresentation<F, E>; 1],
    ) -> [E; 1] {
        unreachable!("not used by this kernel")
    }

    #[inline(always)]
    fn pointwise_eval_forward(&self, _input: &[ExtensionFieldRepresentation<F, E>; 1]) -> [E; 1] {
        unreachable!("not used by this kernel")
    }

    fn pointwise_eval_by_ref(&self, _input: [&ExtensionFieldRepresentation<F, E>; 1]) -> [E; 1] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, 1, 1>
    for ExtensionCopyGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        S: super::EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: super::EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        _sources: &[S; 1],
        output_sources: &[SOUT; 1],
        batch_challenges: &[E; 1],
    ) -> [E; 2] {
        // there is no difference for input or output
        let output_f0 = output_sources[0].get_f0_only(index).into_value();
        let mut eval_c0 = batch_challenges[0];
        eval_c0.mul_assign(&output_f0);

        // result[1] = 0 because the quadratic coefficient is 0 for a linear function
        [eval_c0, E::ZERO]
    }

    #[inline(always)]
    fn evaluate<
        S: super::EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[S; 1],
        batch_challenges: &[E; 1],
    ) -> [E; 2] {
        if EXPLICIT_FORM {
            // For explicit form (final round), return [kernel(f0), kernel(f1)]
            // For Copy, kernel is identity, so this is just [f0, f1]
            let [f0, f1] = sources[0].get_two_points::<true>(index);
            let f0_val = f0.into_value();
            let f1_val = f1.into_value();
            let mut eval_c0 = batch_challenges[0];
            eval_c0.mul_assign(&f0_val);
            let mut eval_c1 = batch_challenges[0];
            eval_c1.mul_assign(&f1_val);
            [eval_c0, eval_c1]
        } else {
            // For non-explicit form (intermediate rounds), return [f0, 0]
            // The quadratic coefficient is 0 for a linear function
            if S::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
                let [f0, _] = sources[0].get_two_points::<EXPLICIT_FORM>(index);
                let mut eval_c0 = batch_challenges[0];
                eval_c0.mul_assign(&f0.into_value());
                [eval_c0, E::ZERO]
            } else {
                let f0 = sources[0].get_f0_only(index).into_value();
                let mut eval_c0 = batch_challenges[0];
                eval_c0.mul_assign(&f0);
                [eval_c0, E::ZERO]
            }
        }
    }
}
