use super::*;

#[derive(Debug)]
pub struct PairwiseProductDimensionReducingGKRRelation {
    pub input: GKRAddress,
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for PairwiseProductDimensionReducingGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![self.input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![self.output],
        }
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        input_trace_len: usize,
        worker: &Worker,
    ) {
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        let kernel = PairwiseProductDimensionReducingGKRRelationKernel::default();
        forward_evaluate_dimension_reducing_kernel(
            &kernel,
            &inputs,
            storage,
            expected_output_layer,
            input_trace_len,
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
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        let kernel = PairwiseProductDimensionReducingGKRRelationKernel::default();
        evaluate_single_dimension_reducing_kernel(
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
#[derive(Default)]
pub struct PairwiseProductDimensionReducingGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> DimensionReducingEvaluationKernel<F, E, 1, 1>
    for PairwiseProductDimensionReducingGKRRelationKernel<F, E>
{
    fn pointwise_eval(
        &self,
        a: &[ExtensionFieldRepresentation<F, E>; 1],
        b: &[ExtensionFieldRepresentation<F, E>; 1],
    ) -> [E; 1] {
        let mut a = a[0];
        a.repr_mul_assign::<false>(&b[0]);
        [a.into_value()]
    }
}
