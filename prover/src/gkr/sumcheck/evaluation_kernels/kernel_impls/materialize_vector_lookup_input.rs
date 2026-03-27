use super::*;
use cs::definitions::{gkr::NoFieldVectorLookupRelation, GKRAddress};

#[derive(Debug)]
pub struct MaterializeVectoLookupInputGKRRelation<F: PrimeField, E: FieldExtension<F> + Field> {
    pub kernel: MaterializeVectoLookupInputGKRRelationKernel<F, E>,
    pub inputs: Vec<GKRAddress>,
    pub output: GKRAddress,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> MaterializeVectoLookupInputGKRRelation<F, E> {
    pub fn new(
        input: &NoFieldVectorLookupRelation,
        output: GKRAddress,
        lookup_multiplicative_challenge: E,
    ) -> Self {
        let mut remapper = DenseInputRemapper::default();
        let mut inputs = vec![];
        let mut kernel = MaterializeVectoLookupInputGKRRelationKernel::<F, E> {
            linear_parts: vec![],
            constant_offset: E::ZERO,
            _marker: core::marker::PhantomData,
        };

        let mut challenge_power = E::ONE;
        for (_column_idx, column) in input.columns.iter().enumerate() {
            for (c, a) in column.linear_terms.iter() {
                let (is_new, a_offset) = remapper.remap(*a);
                if is_new {
                    assert_eq!(a_offset, inputs.len());
                    assert_eq!(a_offset, kernel.linear_parts.len());
                    inputs.push(*a);
                    let mut t = challenge_power;
                    t.mul_assign_by_base(&F::from_u32_with_reduction(*c as u32));

                    kernel.linear_parts.push(t);
                } else {
                    assert!(a_offset < inputs.len());
                    assert!(a_offset < inputs.len());
                }
            }
            // constant part
            let mut t = challenge_power;
            t.mul_assign_by_base(&F::from_u32_with_reduction(column.constant));
            kernel.constant_offset.add_assign(&t);

            challenge_power.mul_assign(&lookup_multiplicative_challenge);
        }

        Self {
            inputs,
            kernel,
            output,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for MaterializeVectoLookupInputGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: self.inputs.clone(),
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: vec![self.output],
        }
    }

    fn evaluate_forward_over_storage(
        &self,
        _storage: &mut GKRStorage<F, E>,
        _expected_output_layer: usize,
        _trace_len: usize,
        _worker: &Worker,
    ) {
        unreachable!();
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
        // println!("Evaluating {}", std::any::type_name::<Self>());

        assert_eq!(
            batch_challenges.len(),
            <Self as BatchedGKRKernel<F, E>>::num_challenges(self)
        );
        let kernel = &self.kernel;
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        evaluate_single_input_kernel_with_base_inputs(
            kernel,
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

#[derive(Debug)]
// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct MaterializeVectoLookupInputGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field>
{
    pub linear_parts: Vec<E>,
    pub constant_offset: E,
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernelCore<F, E, 1>
    for MaterializeVectoLookupInputGKRRelationKernel<F, E>
{
    #[inline]
    fn pointwise_eval(&self, input: &[E]) -> [E; 1] {
        // verifier-sensitive
        unsafe {
            let mut result = self.constant_offset;
            // just evaluate at the point
            for (a, coeff) in self.linear_parts.iter().enumerate() {
                debug_assert!(a < input.len());
                #[cfg(feature = "gkr_self_checks")]
                assert!(a < input.len());

                let mut contribution = *input.get_unchecked(a);
                contribution.mul_assign(coeff);
                result.add_assign(&contribution);
            }

            [result]
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernel<F, E, 1>
    for MaterializeVectoLookupInputGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        output_sources: &[SOUT],
        batch_challenges: &[E],
        _ctx: &R0::CollapseContext,
        out_collapse_ctx: &ROUT::CollapseContext,
    ) -> [E; 2] {
        debug_assert_eq!(output_sources.len(), 1);
        let mut result = [E::ZERO; 2];
        // half if the work is just an output
        result[0] = output_sources[0]
            .get_f0_only(index)
            .collapse_into_ext_with_challenge(out_collapse_ctx, &batch_challenges[0]);

        // and linear part doesn't contribute to quadratic coefficient. We may still have to access(!) source to trigger folding
        if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            for (a, _challenge) in self.linear_parts.iter().enumerate() {
                let _ = r0_sources[a].get_f0_and_f1(index);
            }
        }

        result
    }

    #[inline(always)]
    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        batch_challenges: &[E],
        ctx: &R0::CollapseContext,
    ) -> [E; 2] {
        let mut result = [E::ZERO; 2];

        if EXPLICIT_FORM {
            // just evaluate at the point
            for (a, coeff) in self.linear_parts.iter().enumerate() {
                let a_val = r0_sources[a].get_two_points::<true>(index);

                for i in 0..2 {
                    let contribution = a_val[i].mul_by_ext::<false>(coeff, ctx);
                    result[i].add_assign(&contribution);
                }
            }

            result[0].add_assign(&self.constant_offset);
            result[1].add_assign(&self.constant_offset);
        } else {
            if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
                for (a, coeff) in self.linear_parts.iter().enumerate() {
                    let [a, _] = r0_sources[a].get_two_points::<EXPLICIT_FORM>(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let contribution = a.mul_by_ext::<true>(coeff, ctx);
                    result[0].add_assign(&contribution);
                }
            } else {
                for (a, coeff) in self.linear_parts.iter().enumerate() {
                    let a = r0_sources[a].get_f0_only(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let contribution = a.mul_by_ext::<true>(coeff, ctx);
                    result[0].add_assign(&contribution);
                }
            }

            result[0].add_assign(&self.constant_offset);
        }

        result[0].mul_assign(&batch_challenges[0]);
        result[1].mul_assign(&batch_challenges[0]);

        result
    }
}
