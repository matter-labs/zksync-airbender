use crate::definitions::sumcheck_kernel::fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore;

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
    MixedFieldsInOutFixedSizesEvaluationKernelCore<F, E, 1, 1, 1>
    for MaskIntoIdentityProductGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 1],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
        ctx: &RB::CollapseContext,
    ) -> [E; 1] {
        pointwise_eval_impl(input, ext_input, ctx)
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

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 1],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
        ctx: &RB::CollapseContext,
    ) -> [E; 1] {
        pointwise_eval_quadratic_only_impl(input, ext_input, ctx)
    }

    fn pointwise_eval_by_ref<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: [&RB; 1],
        _ext_input: [&ExtensionFieldRepresentation<F, E>; 1],
        _ctx: &RB::CollapseContext,
    ) -> [E; 1] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 1, 1, 1>
    for MaskIntoIdentityProductGKRRelationKernel<F, E>
{
}

#[inline(always)]
fn pointwise_eval_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 1],
    ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
    ctx: &RB::CollapseContext,
) -> [E; 1] {
    // input(X) * mask(X) + (1 - mask(X)) -> (input(X) - 1) * mask(X) + 1
    let [mask] = input;
    let [val] = ext_input;

    let mut val = val.into_value();
    val.sub_assign_base(&F::ONE);
    let mut val = mask.mul_by_ext::<true>(&val, ctx);
    val.add_assign_base(&F::ONE);

    [val]
}

#[inline(always)]
fn pointwise_eval_quadratic_only_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RB: EvaluationRepresentation<F, E>,
>(
    input: &[RB; 1],
    ext_input: &[ExtensionFieldRepresentation<F, E>; 1],
    ctx: &RB::CollapseContext,
) -> [E; 1] {
    // input(X) * mask(X) + (1 - mask(X)) -> input(X) * mask(X)
    let [mask] = input;
    let [val] = ext_input;
    let val = mask.mul_by_ext::<true>(&val.value, ctx);

    [val]
}
