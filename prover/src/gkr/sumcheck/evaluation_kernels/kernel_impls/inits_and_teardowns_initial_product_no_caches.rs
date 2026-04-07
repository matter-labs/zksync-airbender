use super::*;
use crate::gkr::prover::forward_loop::utils::inits_or_teardowns_as_flattened_relation;
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;

#[derive(Debug)]
pub struct InitsAndTeardownsInitialProductWithoutCachesGKRRelation {
    pub inputs: InitsOrTeardownsTimestampAndValue,
    pub setup: [GKRAddress; 2],
    pub address_high_bits: [u32; 2],
    pub address_high_bits_shift: u32,
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for InitsAndTeardownsInitialProductWithoutCachesGKRRelation
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
        let mut term = BatchedGKRTermDescription::default();
        match self.inputs {
            InitsOrTeardownsTimestampAndValue::Init => {
                let a = inits_or_teardowns_as_flattened_relation(
                    None,
                    self.setup,
                    self.address_high_bits[0],
                    self.address_high_bits_shift,
                    &challenge_constants.external_challenges,
                );
                let b = inits_or_teardowns_as_flattened_relation(
                    None,
                    self.setup,
                    self.address_high_bits[1],
                    self.address_high_bits_shift,
                    &challenge_constants.external_challenges,
                );
                term.add_product_of_linear_base_terms(a, b);
            }
            InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } => {
                let a = inits_or_teardowns_as_flattened_relation(
                    Some((
                        lhs_timestamp.map(GKRAddress::BaseLayerMemory),
                        lhs_value.map(GKRAddress::BaseLayerMemory),
                    )),
                    self.setup,
                    self.address_high_bits[0],
                    self.address_high_bits_shift,
                    &challenge_constants.external_challenges,
                );
                let b = inits_or_teardowns_as_flattened_relation(
                    Some((
                        rhs_timestamp.map(GKRAddress::BaseLayerMemory),
                        rhs_value.map(GKRAddress::BaseLayerMemory),
                    )),
                    self.setup,
                    self.address_high_bits[1],
                    self.address_high_bits_shift,
                    &challenge_constants.external_challenges,
                );
                term.add_product_of_linear_base_terms(a, b);
            }
        }

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
