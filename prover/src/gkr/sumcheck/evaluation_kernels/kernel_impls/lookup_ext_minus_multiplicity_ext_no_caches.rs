use super::*;
use crate::gkr::prover::forward_loop::utils::vector_lookup_as_flattened_relation;
use cs::definitions::{gkr::NoFieldVectorLookupRelation, GKRAddress};
use worker::Worker;

#[derive(Debug)]
pub struct LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation {
    pub input: NoFieldVectorLookupRelation,
    pub setup: (GKRAddress, Box<[GKRAddress]>),
    pub outputs: [GKRAddress; 2],
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        // 1/(b + gamma) - c/(d + gamma) -> ((d+gamma) - c*(b+gamma)), (b+gamma) * (d+gamma)
        let b = &self.input;
        let (c, d) = &self.setup;
        assert_eq!(b.columns.len(), d.len());

        let b = vector_lookup_as_flattened_relation::<F, E, true>(
            b,
            challenge_constants.lookup_challenges_multiplicative_part,
            challenge_constants.lookup_challenges_additive_part,
        );

        let mut d_terms = BTreeMap::new();
        let mut challenge = E::ONE;
        for el in d.iter() {
            assert!(d_terms.insert(*el, challenge).is_none());
            challenge.mul_assign(&challenge_constants.lookup_challenges_multiplicative_part);
        }
        let d = (d_terms, challenge_constants.lookup_challenges_additive_part);
        let c = (BTreeMap::from_iter([(*c, E::MINUS_ONE)]), E::ZERO);

        let mut num_term = BatchedGKRTermDescription::default();
        num_term.add_linear_base_terms(d.clone());
        num_term.add_product_of_linear_base_terms(c, b.clone());
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = BatchedGKRTermDescription::default();
        den_term.add_product_of_linear_base_terms(b, d);
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }

    fn get_inputs(&self) -> GKRInputs {
        unimplemented!("not used");
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
