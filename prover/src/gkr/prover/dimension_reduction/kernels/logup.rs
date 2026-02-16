use super::*;

#[derive(Debug)]
pub struct LookupPairDimensionReducingGKRRelation {
    pub inputs: [GKRAddress; 2], // [[a, b], [c, d]] -> a/b + c/d
    pub outputs: [GKRAddress; 2],
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupPairDimensionReducingGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: self.inputs.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: self.outputs.to_vec(),
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

        let kernel = LookupPairDimensionReducingGKRRelationKernel::default();
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

        let kernel = LookupPairDimensionReducingGKRRelationKernel::default();
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

#[derive(Default)]
pub struct LookupPairDimensionReducingGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field>
{
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> DimensionReducingEvaluationKernel<F, E, 2, 2>
    for LookupPairDimensionReducingGKRRelationKernel<F, E>
{
    fn pointwise_eval(
        &self,
        pair_0: &[ExtensionFieldRepresentation<F, E>; 2],
        pair_1: &[ExtensionFieldRepresentation<F, E>; 2],
    ) -> [E; 2] {
        let [a, b] = pair_0.map(|el| el.into_value());
        let [c, d] = pair_1.map(|el| el.into_value());
        // a/b + c/d = (a*d + c*b) / (b*d)
        let mut num = a;
        num.mul_assign(&d);
        let mut cb = c;
        cb.mul_assign(&b);
        num.add_assign(&cb);

        let mut den = b;
        den.mul_assign(&d);
        [num, den]
    }
}
