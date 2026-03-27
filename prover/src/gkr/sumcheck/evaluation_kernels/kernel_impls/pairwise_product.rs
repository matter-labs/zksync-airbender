use crate::definitions::sumcheck_kernel::fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct SameSizeProductGKRRelation {
    pub inputs: [GKRAddress; 2],
    pub output: GKRAddress,
}

// impl SameSizeProductGKRRelation {
//     /// Validates that neither input is from a cache, output is not cached
//     #[inline]
//     fn validate(&self) -> bool {
//         !self.inputs[0].is_cache() && !self.inputs[1].is_cache() && !self.output.is_cache()
//     }
// }

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for SameSizeProductGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        // debug_assert!(self.validate());
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: self.inputs.to_vec(),
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
        let kernel = ProductGKRRelationKernel::default();
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
        let kernel = ProductGKRRelationKernel::default();
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

// Shared product kernel (compute a * b)
#[derive(Default, Debug)]
pub struct ProductGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernelCore<F, E, 2, 1>
    for ProductGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; 2]) -> [E; 1] {
        let [a, b] = input;
        let mut a = *a;
        a.repr_mul_assign::<true>(b);
        [a.into_value()]
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only(
        &self,
        input: &[ExtensionFieldRepresentation<F, E>; 2],
    ) -> [E; 1] {
        self.pointwise_eval(input)
    }

    #[inline(always)]
    fn pointwise_eval_by_ref(&self, _input: [&ExtensionFieldRepresentation<F, E>; 2]) -> [E; 1] {
        todo!();
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, 2, 1> for ProductGKRRelationKernel<F, E>
{
}
