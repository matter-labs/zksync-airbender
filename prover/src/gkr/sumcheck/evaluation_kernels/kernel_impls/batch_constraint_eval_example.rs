use cs::definitions::GKRAddress;

use super::*;

pub struct BatchConstraintEvalGKRRelation<F: PrimeField, E: FieldExtension<F> + PrimeField> {
    pub quadratic_parts: Vec<((GKRAddress, GKRAddress), Vec<(F, usize)>)>,
    pub linear_parts: Vec<(GKRAddress, Vec<(F, usize)>)>,
    pub num_memory_polys: usize,
    pub num_witness_polys: usize,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + PrimeField> BatchConstraintEvalGKRRelation<F, E> {
    pub fn make_kernel(
        &self,
        challenges_for_constraints: &[E],
    ) -> BatchConstraintEvalGKRRelationKernel<F, E> {
        // this remapping is memory || witness || setup, and it should be consistent with selection order
        let mut quadratic_parts = Vec::with_capacity(self.quadratic_parts.len());
        for ((a, b), set) in self.quadratic_parts.iter() {
            let a_offset = match *a {
                GKRAddress::BaseLayerMemory(offset) => offset,
                GKRAddress::BaseLayerWitness(offset) => offset + self.num_memory_polys,
                GKRAddress::Setup(offset) => {
                    offset + self.num_memory_polys + self.num_witness_polys
                }
                _ => {
                    unreachable!()
                }
            };
            let b_offset = match *b {
                GKRAddress::BaseLayerMemory(offset) => offset,
                GKRAddress::BaseLayerWitness(offset) => offset + self.num_memory_polys,
                GKRAddress::Setup(offset) => {
                    offset + self.num_memory_polys + self.num_witness_polys
                }
                _ => {
                    unreachable!()
                }
            };
            let mut total_prefactor = E::ZERO;
            for (c, pow) in set.iter() {
                let mut t = challenges_for_constraints[*pow];
                t.mul_assign_by_base(c);
                total_prefactor.add_assign(&t);
            }
            quadratic_parts.push(((a_offset, b_offset), total_prefactor));
        }

        let linear_parts = vec![]; // todo!();

        BatchConstraintEvalGKRRelationKernel {
            quadratic_parts,
            linear_parts,
            _marker: core::marker::PhantomData,
        }
    }
}

// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct BatchConstraintEvalGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + PrimeField> {
    pub quadratic_parts: Vec<((usize, usize), E)>,
    pub linear_parts: Vec<(usize, E)>,
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + PrimeField>
    SingleInputTypeBatchSumcheckEvaluationKernel<F, E>
    for BatchConstraintEvalGKRRelationKernel<F, E>
{
    fn num_challenges(&self) -> usize {
        1
    }
    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        _output_sources: &[SOUT],
        batch_challenges: &[E],
    ) -> [E; 2] {
        let mut result = [E::ZERO; 2];
        let ctx = r0_sources[0].get_collapse_context();
        for ((a, b), challenge) in self.quadratic_parts.iter() {
            let a = r0_sources[*a].get_f1_minus_f0_only(index);
            let b = r0_sources[*b].get_f1_minus_f0_only(index);
            {
                let mut t = a;
                t.repr_mul_assign::<true>(&b);
                let contribution = t.collapse_for_batch_eval(ctx, challenge);
                result[1].add_assign(&contribution);
            }
        }
        // and linear part doesn't contribute to quadratic coefficient. We may still have to access(!) source to trigger folding
        if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            for (a, _challenge) in self.linear_parts.iter() {
                let _a = r0_sources[*a].get_f0_and_f1(index);
            }
        }
        result[0].mul_assign(&batch_challenges[0]);
        result[1].mul_assign(&batch_challenges[0]);

        result
    }

    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        batch_challenges: &[E],
    ) -> [E; 2] {
        let mut result = [E::ZERO; 2];
        let ctx = r0_sources[0].get_collapse_context();
        for ((a, b), challenge) in self.quadratic_parts.iter() {
            let a = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
            let b = r0_sources[*b].get_two_points::<EXPLICIT_FORM>(index);
            for i in 0..2 {
                let mut t = a[i];
                t.repr_mul_assign::<true>(&b[i]);
                let contribution = t.collapse_for_batch_eval(ctx, challenge);
                result[i].add_assign(&contribution);
            }
        }
        for (a, challenge) in self.linear_parts.iter() {
            let a = r0_sources[*a].get_f0_only(index);
            // and linear part doesn't contribute to quadratic coefficient

            // TODO: verify that it's also valid for the last explicit sumcheck round
            {
                let contribution = a.collapse_for_batch_eval(ctx, challenge);
                result[0].add_assign(&contribution);
            }
        }
        result[0].mul_assign(&batch_challenges[0]);
        result[1].mul_assign(&batch_challenges[0]);

        result
    }
}
