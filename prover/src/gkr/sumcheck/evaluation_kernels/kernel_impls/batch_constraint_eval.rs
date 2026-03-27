use super::*;
use cs::{definitions::GKRAddress, gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation};

#[derive(Debug)]
pub struct BatchConstraintEvalGKRRelation<F: PrimeField, E: FieldExtension<F> + Field> {
    pub kernel: BatchConstraintEvalGKRRelationKernel<F, E>,
    pub inputs: Vec<GKRAddress>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchConstraintEvalGKRRelation<F, E> {
    pub fn new(
        input: &NoFieldMaxQuadraticConstraintsGKRRelation,
        challenge_for_constraints: E,
    ) -> Self {
        let mut remapper = DenseInputRemapper::default();
        let mut inputs = vec![];
        let mut kernel = BatchConstraintEvalGKRRelationKernel {
            quadratic_parts: vec![],
            linear_parts: vec![],
            constant_offset: E::ZERO,
            _marker: core::marker::PhantomData,
        };

        for ((a, b), set) in input.quadratic_terms.iter() {
            let (is_new, a_offset) = remapper.remap(*a);
            if is_new {
                inputs.push(*a);
            }

            let b_offset = if *a != *b {
                let (is_new, b_offset) = remapper.remap(*b);

                if is_new {
                    inputs.push(*b);
                }

                b_offset
            } else {
                a_offset
            };

            let mut total_prefactor = E::ZERO;
            for (c, pow) in set.iter() {
                let mut t = challenge_for_constraints.pow(*pow as u32);
                let c = F::from_u32_with_reduction(*c);
                t.mul_assign_by_base(&c);
                total_prefactor.add_assign(&t);
            }
            kernel
                .quadratic_parts
                .push(((a_offset, b_offset), total_prefactor));
        }

        for (a, set) in input.linear_terms.iter() {
            let (is_new, a_offset) = remapper.remap(*a);
            if is_new {
                inputs.push(*a);
            }
            let mut total_prefactor = E::ZERO;
            for (c, pow) in set.iter() {
                let mut t = challenge_for_constraints.pow(*pow as u32);
                let c = F::from_u32_with_reduction(*c);
                t.mul_assign_by_base(&c);
                total_prefactor.add_assign(&t);
            }
            kernel.linear_parts.push((a_offset, total_prefactor));
        }

        for (c, pow) in input.constants.iter() {
            let mut t = challenge_for_constraints.pow(*pow as u32);
            let c = F::from_u32_with_reduction(*c);
            t.mul_assign_by_base(&c);
            kernel.constant_offset.add_assign(&t);
        }

        Self { inputs, kernel }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for BatchConstraintEvalGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: self.inputs.clone(),
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
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
pub struct BatchConstraintEvalGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    pub quadratic_parts: Vec<((usize, usize), E)>,
    pub linear_parts: Vec<(usize, E)>,
    pub constant_offset: E,
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernelCore<F, E, 1>
    for BatchConstraintEvalGKRRelationKernel<F, E>
{
    #[inline]
    fn pointwise_eval(&self, input: &[E]) -> [E; 1] {
        // verifier-sensitive
        unsafe {
            let mut result = self.constant_offset;
            for ((a, b), challenge) in self.quadratic_parts.iter() {
                debug_assert!(*a < input.len());
                #[cfg(feature = "gkr_self_checks")]
                assert!(*a < input.len());

                let mut contribution = *input.get_unchecked(*a);

                if *a != *b {
                    debug_assert!(*b < input.len());
                    #[cfg(feature = "gkr_self_checks")]
                    assert!(*b < input.len());

                    let b = input.get_unchecked(*b);
                    contribution.mul_assign(b);
                } else {
                    contribution.square();
                };
                contribution.mul_assign(challenge);
                result.add_assign(&contribution);
            }
            // just evaluate at the point
            for (a, challenge) in self.linear_parts.iter() {
                debug_assert!(*a < input.len());
                #[cfg(feature = "gkr_self_checks")]
                assert!(*a < input.len());

                let mut contribution = *input.get_unchecked(*a);
                contribution.mul_assign(challenge);
                result.add_assign(&contribution);
            }

            [result]
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernel<F, E, 1>
    for BatchConstraintEvalGKRRelationKernel<F, E>
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
        _output_sources: &[SOUT],
        batch_challenges: &[E],
        ctx: &R0::CollapseContext,
        _out_collapse_ctx: &ROUT::CollapseContext,
    ) -> [E; 2] {
        assert!(_output_sources.is_empty());
        let mut result = [E::ZERO; 2];

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut buffers = [E::ZERO; 2];
            for ((a, b), challenge) in self.quadratic_parts.iter() {
                let (a, b) = if *a != *b {
                    let a = r0_sources[*a].get_two_points::<true>(index);
                    let b = r0_sources[*b].get_two_points::<true>(index);

                    (a, b)
                } else {
                    let a = r0_sources[*a].get_two_points::<true>(index);
                    (a, a)
                };

                for i in 0..2 {
                    let mut t = a[i];
                    t.repr_mul_assign::<true>(&b[i]);
                    let contribution = t.collapse_into_ext_with_challenge(ctx, challenge);
                    buffers[i].add_assign(&contribution);
                }
            }
            for (a, challenge) in self.linear_parts.iter() {
                let [a, b] = r0_sources[*a].get_two_points::<true>(index);

                let contribution = a.collapse_into_ext_with_challenge(ctx, challenge);
                buffers[0].add_assign(&contribution);

                let contribution = b.collapse_into_ext_with_challenge(ctx, challenge);
                buffers[1].add_assign(&contribution);
            }

            buffers[0].add_assign(&self.constant_offset);
            buffers[1].add_assign(&self.constant_offset);

            for i in 0..2 {
                let part = if i == 0 { "low" } else { "high" };
                assert_eq!(
                    buffers[i],
                    E::ZERO,
                    "unsatisfied for index {} for {} part",
                    index,
                    part
                );
            }
        }

        for ((a, b), challenge) in self.quadratic_parts.iter() {
            let (a, b) = if *a != *b {
                let a = r0_sources[*a].get_f1_minus_f0_only(index);
                let b = r0_sources[*b].get_f1_minus_f0_only(index);

                (a, b)
            } else {
                let a = r0_sources[*a].get_f1_minus_f0_only(index);
                (a, a)
            };

            {
                let mut t = a;
                t.repr_mul_assign::<true>(&b);
                let contribution = t.collapse_into_ext_with_challenge(ctx, challenge);
                result[1].add_assign(&contribution);
            }
        }
        // and linear part doesn't contribute to quadratic coefficient. We may still have to access(!) source to trigger folding
        if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            for (a, _challenge) in self.linear_parts.iter() {
                let _ = r0_sources[*a].get_f0_and_f1(index);
            }
        }
        result[1].mul_assign(&batch_challenges[0]);

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
        for ((a, b), challenge) in self.quadratic_parts.iter() {
            let (a, b) = if *a != *b {
                let a = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
                let b = r0_sources[*b].get_two_points::<EXPLICIT_FORM>(index);

                (a, b)
            } else {
                let a = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
                (a, a)
            };

            for i in 0..2 {
                let mut t = a[i];
                t.repr_mul_assign::<true>(&b[i]);
                let contribution = t.collapse_into_ext_with_challenge(ctx, challenge);
                result[i].add_assign(&contribution);
            }
        }
        if EXPLICIT_FORM {
            // just evaluate at the point
            for (a, challenge) in self.linear_parts.iter() {
                let [a, b] = r0_sources[*a].get_two_points::<true>(index);

                let contribution = a.collapse_into_ext_with_challenge(ctx, challenge);
                result[0].add_assign(&contribution);

                let contribution = b.collapse_into_ext_with_challenge(ctx, challenge);
                result[1].add_assign(&contribution);
            }

            result[0].add_assign(&self.constant_offset);
            result[1].add_assign(&self.constant_offset);
        } else {
            if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
                for (a, challenge) in self.linear_parts.iter() {
                    let [a, _] = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let contribution = a.collapse_into_ext_with_challenge(ctx, challenge);
                    result[0].add_assign(&contribution);
                }
            } else {
                for (a, challenge) in self.linear_parts.iter() {
                    let a = r0_sources[*a].get_f0_only(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let contribution = a.collapse_into_ext_with_challenge(ctx, challenge);
                    result[0].add_assign(&contribution);
                }
            }

            result[0].add_assign(&self.constant_offset);
        }

        result[0].mul_assign(&batch_challenges[0]);
        result[1].mul_assign(&batch_challenges[0]);

        // assert_ne!(result[0], E::ZERO);

        result
    }
}
