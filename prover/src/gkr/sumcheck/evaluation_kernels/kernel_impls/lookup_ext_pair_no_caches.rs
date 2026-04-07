use crate::gkr::prover::forward_loop::utils::vector_lookup_as_flattened_relation;
use cs::definitions::{gkr::NoFieldVectorLookupRelation, GKRAddress};
use worker::Worker;

use super::*;

#[derive(Debug)]
pub struct LookupExtensionPairWithoutCachesGKRRelation {
    pub inputs: [NoFieldVectorLookupRelation; 2],
    pub outputs: [GKRAddress; 2],
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupExtensionPairWithoutCachesGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        unimplemented!("not used");
    }

    fn terms(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        // 1/(b + gamma) + 1/(d + gamma) -> ((d+gamma) + (b+gamma)), (b+gamma) * (d+gamma)
        let [b, d] = &self.inputs;

        let b = vector_lookup_as_flattened_relation::<F, E, true>(
            b,
            challenge_constants.lookup_challenges_multiplicative_part,
            challenge_constants.lookup_challenges_additive_part,
        );

        let d = vector_lookup_as_flattened_relation::<F, E, true>(
            d,
            challenge_constants.lookup_challenges_multiplicative_part,
            challenge_constants.lookup_challenges_additive_part,
        );

        let mut num_term = BatchedGKRTermDescription::default();
        num_term.add_linear_base_terms(b.clone());
        num_term.add_linear_base_terms(d.clone());
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = BatchedGKRTermDescription::default();
        den_term.add_product_of_linear_base_terms(b, d);
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }

    fn evaluate_forward_over_storage(
        &self,
        _storage: &mut GKRStorage<F, E>,
        _expected_output_layer: usize,
        _trace_len: usize,
        _worker: &Worker,
    ) {
        unimplemented!("not used");
    }

    fn evaluate_over_storage<const N: usize>(
        &self,
        _storage: &mut GKRStorage<F, E>,
        _step: usize,
        _batch_challenges: &[E],
        _folding_challenges: &[E],
        _accumulator: &mut [[E; 2]],
        _total_sumcheck_rounds: usize,
        _last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
        _worker: &Worker,
    ) {
        unimplemented!("not used");
    }
}
