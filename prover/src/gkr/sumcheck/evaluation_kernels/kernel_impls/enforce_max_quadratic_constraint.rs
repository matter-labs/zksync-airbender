use super::*;
use cs::{definitions::GKRAddress, gkr_compiler::NoFieldMaxQuadraticGKRRelation};

#[derive(Debug)]
pub struct EnforceSingleMaxQuadraticConstraintGKRRelation {
    pub relation: NoFieldMaxQuadraticGKRRelation,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for EnforceSingleMaxQuadraticConstraintGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        unimplemented!("not used");
    }

    fn terms(
        &self,
        _challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let mut term = BatchedGKRTermDescription::default();

        for (a, other_terms) in self.relation.quadratic_terms.iter() {
            for (c, b) in other_terms.iter() {
                term.add_base_by_base(*a, *b, E::from_base(F::from_u32_unchecked(*c)));
            }
        }

        for (c, b) in self.relation.linear_terms.iter() {
            term.add_linear_with_base(*b, E::from_base(F::from_u32_unchecked(*c)));
        }
        term.add_constant(E::from_base(F::from_u32_unchecked(self.relation.constant)));

        // just no output

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
