use super::*;
use cs::{definitions::GKRAddress, gkr_compiler::NoFieldMaxQuadraticGKRRelation};

#[derive(Debug)]
pub struct MaxQuadraticGKRRelation<F: PrimeField, E: FieldExtension<F> + Field> {
    pub kernel: MaxQuadraticGKRRelationKernel<F, E>,
    pub inputs: Vec<GKRAddress>,
    pub output: GKRAddress,
}

#[derive(Default)]
pub(crate) struct DenseInputRemapper {
    mapping: BTreeMap<GKRAddress, usize>,
}

impl DenseInputRemapper {
    pub(crate) fn remap(&mut self, address: GKRAddress) -> (bool, usize) {
        if let GKRAddress::ScratchSpace(..) = address {
            panic!("Scratch space addresses are not allowed in constraints");
        };
        if let Some(idx) = self.mapping.get(&address).copied() {
            (false, idx)
        } else {
            let idx = self.mapping.len();
            self.mapping.insert(address, idx);

            (true, idx)
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> MaxQuadraticGKRRelation<F, E> {
    pub fn new(input: &NoFieldMaxQuadraticGKRRelation, output: GKRAddress) -> Self {
        let mut remapper = DenseInputRemapper::default();
        let mut inputs = vec![];
        let mut kernel = MaxQuadraticGKRRelationKernel::<F, E> {
            quadratic_parts: vec![],
            linear_parts: vec![],
            constant_offset: F::from_u32_with_reduction(input.constant as u32),
            _marker: core::marker::PhantomData,
        };

        for (a, set) in input.quadratic_terms.iter() {
            let (is_new, a_offset) = remapper.remap(*a);
            if is_new {
                inputs.push(*a);
            }
            let mut compiled_set = vec![];
            for (c, b) in set.iter() {
                let b_offset = if *a != *b {
                    let (is_new, b_offset) = remapper.remap(*b);

                    if is_new {
                        inputs.push(*b);
                    }

                    b_offset
                } else {
                    a_offset
                };
                compiled_set.push((b_offset, F::from_u32_with_reduction(*c as u32)));
            }
            kernel.quadratic_parts.push((a_offset, compiled_set));
        }

        for (c, a) in input.linear_terms.iter() {
            let (is_new, a_offset) = remapper.remap(*a);
            if is_new {
                inputs.push(*a);
            }
            kernel
                .linear_parts
                .push((a_offset, F::from_u32_with_reduction(*c as u32)));
        }

        Self {
            inputs,
            kernel,
            output,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for MaxQuadraticGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: self.inputs.clone(),
            inputs_in_extension: Vec::new(),
            outputs_in_base: vec![self.output],
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
pub struct MaxQuadraticGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    pub quadratic_parts: Vec<(usize, Vec<(usize, F)>)>,
    pub linear_parts: Vec<(usize, F)>,
    pub constant_offset: F,
    _marker: core::marker::PhantomData<E>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernelCore<F, E, 1>
    for MaxQuadraticGKRRelationKernel<F, E>
{
    #[inline]
    fn pointwise_eval(&self, input: &[E]) -> [E; 1] {
        // verifier-sensitive
        unsafe {
            let mut result = E::from_base(self.constant_offset);
            for (a, set) in self.quadratic_parts.iter() {
                debug_assert!(*a < input.len());
                #[cfg(feature = "gkr_self_checks")]
                assert!(*a < input.len());

                let a_value = *input.get_unchecked(*a);

                for (b, coeff) in set.iter() {
                    // Each (b, coeff) term is an independent contribution that starts from
                    // input[a]. Reusing the previous contribution would incorrectly compound
                    // quadratic terms.

                    let mut contribution = a_value;
                    if *a != *b {
                        debug_assert!(*b < input.len());
                        #[cfg(feature = "gkr_self_checks")]
                        assert!(*b < input.len());

                        let b = input.get_unchecked(*b);
                        contribution.mul_assign(b);
                    } else {
                        contribution.square();
                    };
                    contribution.mul_assign_by_base(coeff);
                    result.add_assign(&contribution);
                }
            }
            // just evaluate at the point
            for (a, coeff) in self.linear_parts.iter() {
                debug_assert!(*a < input.len());
                #[cfg(feature = "gkr_self_checks")]
                assert!(*a < input.len());

                let mut contribution = *input.get_unchecked(*a);
                contribution.mul_assign_by_base(coeff);
                result.add_assign(&contribution);
            }

            [result]
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernel<F, E, 1> for MaxQuadraticGKRRelationKernel<F, E>
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
        ctx: &R0::CollapseContext,
        out_collapse_ctx: &ROUT::CollapseContext,
    ) -> [E; 2] {
        debug_assert_eq!(output_sources.len(), 1);
        let mut result = [E::ZERO; 2];
        // half if the work is just an output
        result[0] = output_sources[0]
            .get_f0_only(index)
            .collapse_into_ext_with_challenge(out_collapse_ctx, &batch_challenges[0]);

        // #[cfg(feature = "gkr_self_checks")]
        // {
        //     let mut buffers = [E::ZERO; 2];
        //     for ((a, b), challenge) in self.quadratic_parts.iter() {
        //         let (a, b) = if *a != *b {
        //             let a = r0_sources[*a].get_two_points::<true>(index);
        //             let b = r0_sources[*b].get_two_points::<true>(index);

        //             (a, b)
        //         } else {
        //             let a = r0_sources[*a].get_two_points::<true>(index);
        //             (a, a)
        //         };

        //         for i in 0..2 {
        //             let mut t = a[i];
        //             t.repr_mul_assign::<true>(&b[i]);
        //             let contribution = t.collapse_into_ext_with_challenge(ctx, challenge);
        //             buffers[i].add_assign(&contribution);
        //         }
        //     }
        //     for (a, challenge) in self.linear_parts.iter() {
        //         let [a, b] = r0_sources[*a].get_two_points::<true>(index);

        //         let contribution = a.collapse_into_ext_with_challenge(ctx, challenge);
        //         buffers[0].add_assign(&contribution);

        //         let contribution = b.collapse_into_ext_with_challenge(ctx, challenge);
        //         buffers[1].add_assign(&contribution);
        //     }

        //     buffers[0].add_assign(&self.constant_offset);
        //     buffers[1].add_assign(&self.constant_offset);

        //     for i in 0..2 {
        //         let part = if i == 0 { "low" } else { "high" };
        //         assert_eq!(
        //             buffers[i],
        //             E::ZERO,
        //             "unsatisfied for index {} for {} part",
        //             index,
        //             part
        //         );
        //     }
        // }

        // This accumulator tracks only the quadratic coefficient for the first round.
        // Constant offsets do not contribute to that coefficient, so start from zero.
        let mut tmp: R0 = R0::from_base_constant(F::ZERO);

        for (a, set) in self.quadratic_parts.iter() {
            let a_val = r0_sources[*a].get_f1_minus_f0_only(index);
            for (b, coeff) in set.iter() {
                let b_val = if *a == *b {
                    a_val
                } else {
                    r0_sources[*b].get_f1_minus_f0_only(index)
                };
                let mut t = a_val;
                t.repr_mul_assign::<true>(&b_val);
                let t = t.mul_by_base::<false>(coeff);
                tmp.repr_add_assign::<false>(&t);
            }
        }
        // and linear part doesn't contribute to quadratic coefficient. We may still have to access(!) source to trigger folding
        if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
            for (a, _challenge) in self.linear_parts.iter() {
                let _ = r0_sources[*a].get_f0_and_f1(index);
            }
        }
        result[1] = tmp.collapse_into_ext_with_challenge(ctx, &batch_challenges[0]);

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
        for (a, set) in self.quadratic_parts.iter() {
            let a_val = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
            for (b, coeff) in set.iter() {
                let b_val = if *a == *b {
                    a_val
                } else {
                    r0_sources[*b].get_two_points::<EXPLICIT_FORM>(index)
                };
                for i in 0..2 {
                    let mut t = a_val[i];
                    t.repr_mul_assign::<true>(&b_val[i]);
                    let t = t.mul_by_base::<false>(coeff);
                    let contribution = t.collapse_as_ext_field_element(ctx);
                    result[i].add_assign(&contribution);
                }
            }
        }

        if EXPLICIT_FORM {
            // just evaluate at the point
            for (a, coeff) in self.linear_parts.iter() {
                let a_val = r0_sources[*a].get_two_points::<true>(index);

                for i in 0..2 {
                    let t = a_val[i].mul_by_base::<false>(coeff);
                    let contribution = t.collapse_as_ext_field_element(ctx);
                    result[i].add_assign(&contribution);
                }
            }

            result[0].add_assign_base(&self.constant_offset);
            result[1].add_assign_base(&self.constant_offset);
        } else {
            if S0::SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP {
                for (a, coeff) in self.linear_parts.iter() {
                    let [a, _] = r0_sources[*a].get_two_points::<EXPLICIT_FORM>(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let t = a.mul_by_base::<true>(coeff);
                    let contribution = t.collapse_as_ext_field_element(ctx);
                    result[0].add_assign(&contribution);
                }
            } else {
                for (a, coeff) in self.linear_parts.iter() {
                    let a = r0_sources[*a].get_f0_only(index);
                    // and linear part doesn't contribute to quadratic coefficient

                    let t = a.mul_by_base::<true>(coeff);
                    let contribution = t.collapse_as_ext_field_element(ctx);
                    result[0].add_assign(&contribution);
                }
            }

            result[0].add_assign_base(&self.constant_offset);
        }

        result[0].mul_assign(&batch_challenges[0]);
        result[1].mul_assign(&batch_challenges[0]);

        result
    }
}
