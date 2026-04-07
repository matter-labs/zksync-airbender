use super::*;
use crate::gkr::prover::forward_loop::utils::single_column_lookup_as_flattened_relation;
use cs::definitions::{gkr::NoFieldSingleColumnLookupRelation, GKRAddress};

#[derive(Debug)]
pub struct MaterializeSingleLookupInputGKRRelation {
    pub input: NoFieldSingleColumnLookupRelation,
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for MaterializeSingleLookupInputGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        unimplemented!("not used");
    }

    fn terms(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let inp = single_column_lookup_as_flattened_relation::<F, E, false>(
            &self.input,
            challenge_constants.lookup_challenges_additive_part,
        );

        let mut term = BatchedGKRTermDescription::default();
        term.add_linear_base_terms(inp);
        term.set_base_output(self.output);

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
