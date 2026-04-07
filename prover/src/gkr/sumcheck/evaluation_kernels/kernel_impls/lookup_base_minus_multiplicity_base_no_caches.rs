use cs::definitions::GKRAddress;
use worker::Worker;

use super::*;

#[derive(Debug)]
pub struct LookupBaseMinusMultiplicityByBaseWithoutCachesGKRRelation<
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
    for LookupBaseMinusMultiplicityByBaseWithoutCachesGKRRelation<F, E>
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

    // fn terms(
    //     &self,
    //     challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    // ) -> Vec<BatchedGKRTermDescription<F, E>> {
    //     // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
    //     let (a, b) = &self.masked_input;
    //     let (c, d) = &self.setup;

    //     let b = vector_lookup_as_flattened_relation::<F, E, true>(
    //         b,
    //         challenge_constants.lookup_challenges_multiplicative_part,
    //         challenge_constants.lookup_challenges_additive_part,
    //     );
    //     let a = (BTreeMap::from_iter([(*a, E::ONE)]), E::ZERO);

    //     let mut d_terms = BTreeMap::new();
    //     let mut challenge = E::ONE;
    //     for el in d.iter() {
    //         assert!(d_terms.insert(*el, challenge).is_none());
    //         challenge.mul_assign(&challenge_constants.lookup_challenges_multiplicative_part);
    //     }
    //     let d = (d_terms, challenge_constants.lookup_challenges_additive_part);
    //     let c = (BTreeMap::from_iter([(*c, E::MINUS_ONE)]), E::ZERO);

    //     let mut num_term = BatchedGKRTermDescription::default();
    //     num_term.add_product_of_linear_base_terms(a, b.clone());
    //     num_term.add_product_of_linear_base_terms(c, d.clone());
    //     num_term.set_extension_output(self.outputs[0]);

    //     let mut den_term = BatchedGKRTermDescription::default();
    //     den_term.add_product_of_linear_base_terms(b, d);
    //     den_term.set_extension_output(self.outputs[1]);

    //     vec![num_term, den_term]
    // }

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
