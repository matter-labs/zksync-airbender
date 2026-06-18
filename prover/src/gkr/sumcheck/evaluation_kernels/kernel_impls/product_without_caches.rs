use crate::gkr::prover::forward_loop::utils::memory_query_as_flattened_relation;

use super::*;
use cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation;

#[derive(Debug)]
pub struct SameSizeProductGKRRelationWithoutCaches {
    pub inputs: [NoFieldSpecialMemoryContributionRelation; 2],
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for SameSizeProductGKRRelationWithoutCaches
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        unreachable!("not used");

        // GKRInputs {
        //     inputs_in_base: Vec::new(),
        //     inputs_in_extension: self.inputs.to_vec(),
        //     outputs_in_base: Vec::new(),
        //     outputs_in_extension: vec![self.output],
        // }
    }

    fn terms(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let [a, b] = &self.inputs;
        let mut term = BatchedGKRTermDescription::default();
        term.add_product_of_linear_base_terms(
            memory_query_as_flattened_relation(a, &challenge_constants.external_challenges),
            memory_query_as_flattened_relation(b, &challenge_constants.external_challenges),
        );

        term.set_extension_output(self.output);

        vec![term]
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
