use crate::definitions::sumcheck_kernel::fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupPairGKRRelation {
    pub inputs: [[GKRAddress; 2]; 2], // [[a, b], [c, d]] -> a/b + c/d
    pub outputs: [GKRAddress; 2],
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E> for LookupPairGKRRelation {
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: [
                self.inputs[0][0],
                self.inputs[0][1],
                self.inputs[1][0],
                self.inputs[1][1],
            ]
            .to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: self.outputs.to_vec(),
        }
    }

    fn terms(
        &self,
        _challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let [[a, b], [c, d]] = self.inputs;

        let mut num_term = BatchedGKRTermDescription::default();
        num_term.add_ext_by_ext(a, d, E::ONE);
        num_term.add_ext_by_ext(b, c, E::ONE);
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = BatchedGKRTermDescription::default();
        den_term.add_ext_by_ext(b, d, E::ONE);
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
        let kernel = LookupAdditionGKRRelationKernel::default();
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
        let kernel = LookupAdditionGKRRelationKernel::default();
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
pub struct LookupAdditionGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernelCore<F, E, 4, 2>
    for LookupAdditionGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; 4]) -> [E; 2] {
        let [a, b, c, d] = input.each_ref().map(|x| x.into_value());
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

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only(
        &self,
        input: &[ExtensionFieldRepresentation<F, E>; 4],
    ) -> [E; 2] {
        self.pointwise_eval(input)
    }

    fn pointwise_eval_by_ref(&self, _input: [&ExtensionFieldRepresentation<F, E>; 4]) -> [E; 2] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, 4, 2>
    for LookupAdditionGKRRelationKernel<F, E>
{
}
