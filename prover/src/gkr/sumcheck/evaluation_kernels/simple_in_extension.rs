use crate::{
    definitions::sumcheck_kernel::fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore,
    gkr::{prover::apply_row_wise, sumcheck::access_and_fold::ExtensionFieldPoly},
};

use super::*;
use std::mem::MaybeUninit;

pub trait ExtensionFieldInOutFixedSizesEvaluationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
>: Send + Sync + ExtensionFieldInOutFixedSizesEvaluationKernelCore<F, E, IN, OUT>
{
    #[inline(always)]
    fn evaluate_forward<S: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>>(
        &self,
        index: usize,
        sources: &[S; IN],
    ) -> [E; OUT] {
        assert!(IN > 0);
        assert!(OUT > 0);
        let p0s = std::array::from_fn(|i| sources[i].get_at_index(index));
        let eval = self.pointwise_eval_forward(&p0s);

        eval
    }

    #[inline(always)]
    fn evaluate_first_round<
        S: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[S; IN],
        output_sources: &[SOUT; OUT],
        batch_challenges: &[E; OUT],
    ) -> [E; 2] {
        assert!(IN > 0);
        assert!(OUT > 0);
        unsafe {
            let mut result = [const { MaybeUninit::uninit() }; 2];
            // we have access to output
            {
                let outputs = output_sources.each_ref().map(|el| el.get_f0_only(index));
                let mut eval = batch_challenges[0];
                eval.mul_assign(&outputs[0].into_value());
                for i in 1..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign(&outputs[i].into_value());
                    eval.add_assign(&t);
                }
                result[0].write(eval);
            }
            {
                let sources = sources.each_ref().map(|el| el.get_f1_minus_f0_only(index));
                let evals = self.pointwise_eval_quadratic_term_only(&sources);
                let mut eval = batch_challenges[0];
                eval.mul_assign(&evals[0]);
                for i in 1..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign(&evals[i]);
                    eval.add_assign(&t);
                }
                result[1].write(eval);
            }

            result.map(|el| el.assume_init())
        }
    }

    #[inline(always)]
    fn evaluate<
        S: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[S; IN],
        batch_challenges: &[E; OUT],
    ) -> [E; 2] {
        assert!(IN > 0);
        assert!(OUT > 0);
        unsafe {
            let mut result = [const { MaybeUninit::uninit() }; 2];
            let mut p0s = [const { MaybeUninit::uninit() }; IN];
            let mut p1s = [const { MaybeUninit::uninit() }; IN];
            for i in 0..IN {
                let [f0, f1] = sources[i].get_two_points::<EXPLICIT_FORM>(index);
                p0s[i].write(f0);
                p1s[i].write(f1);
            }
            let p0s = p0s.map(|el| el.assume_init());
            let p1s = p1s.map(|el| el.assume_init());

            // all terms
            {
                let evals = self.pointwise_eval(&p0s);
                let mut eval = batch_challenges[0];
                eval.mul_assign(&evals[0]);
                for i in 1..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign(&evals[i]);
                    eval.add_assign(&t);
                }
                result[0].write(eval);
            }

            // quadratic ony only, unless we want plain evaluations
            {
                let evals = if EXPLICIT_FORM {
                    self.pointwise_eval(&p1s)
                } else {
                    self.pointwise_eval_quadratic_term_only(&p1s)
                };
                let mut eval = batch_challenges[0];
                eval.mul_assign(&evals[0]);
                for i in 1..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign(&evals[i]);
                    eval.add_assign(&t);
                }
                result[1].write(eval);
            }

            result.map(|el| el.assume_init())
        }
    }
}

pub fn forward_evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, IN, OUT>,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    assert!(trace_len.is_power_of_two());
    unsafe {
        let mut inputs = inputs.clone();
        let outputs = std::mem::replace(&mut inputs.outputs_in_extension, vec![]);
        assert_eq!(outputs.len(), OUT);
        for output in outputs.iter() {
            output.assert_as_layer(expected_output_layer);
        }
        let sources = storage.get_for_sumcheck_round_0(&inputs);
        let mut destinations = Vec::with_capacity(outputs.len());
        for _ in 0..outputs.len() {
            destinations.push(Box::<[E]>::new_uninit_slice(trace_len));
        }
        let mut destinations_refs = Vec::with_capacity(outputs.len());
        for el in destinations.iter_mut() {
            destinations_refs.push(&mut el[..]);
        }

        let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();

        apply_row_wise::<F, _>(
            vec![],
            destinations_refs,
            trace_len,
            worker,
            |_, ext_dest, chunk_start, chunk_size| {
                assert_eq!(ext_dest.len(), OUT);
                let mut destinations: [&mut [MaybeUninit<E>]; OUT] = ext_dest.try_into().unwrap();
                for index in 0..chunk_size {
                    let absolute_index = chunk_start + index;
                    let value = kernel.evaluate_forward(absolute_index, inputs);
                    for (dst, val) in destinations.iter_mut().zip(value.into_iter()) {
                        dst[index].write(val);
                    }
                }
            },
        );

        for (output, destination) in outputs.into_iter().zip(destinations.into_iter()) {
            let values = destination.assume_init();
            storage.insert_extension_at_layer(
                expected_output_layer,
                output,
                ExtensionFieldPoly::new(values),
            );
        }
    }
}

pub fn evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, IN, OUT>,
    const N: usize,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    step: usize,
    batch_challenges: &[E],
    folding_challenges: &[E],
    accumulator: &mut [[E; 2]],
    total_sumcheck_rounds: usize,
    last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
    worker: &Worker,
) {
    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());
    unsafe {
        match step {
            0 => {
                let sources = storage.get_for_sumcheck_round_0(inputs);
                assert!(sources.base_field_inputs.is_empty());
                assert!(sources.base_field_outputs.is_empty());
                if sources.extension_field_outputs.is_empty() == false {
                    assert_eq!(sources.extension_field_inputs.len(), IN);
                    assert_eq!(sources.extension_field_outputs.len(), OUT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
                    let outputs = sources
                        .extension_field_outputs
                        .as_array()
                        .unwrap_unchecked();
                    let challenges = batch_challenges.as_array().unwrap_unchecked();

                    apply_row_wise::<F, _>(
                        vec![],
                        vec![accumulator],
                        work_size,
                        worker,
                        |_, mut ext_dest, chunk_start, chunk_size| {
                            assert_eq!(ext_dest.len(), 1);
                            let accumulator = ext_dest.pop().unwrap();
                            for index in 0..chunk_size {
                                let absolute_index = chunk_start + index;
                                let value = kernel.evaluate_first_round(
                                    absolute_index,
                                    inputs,
                                    outputs,
                                    challenges,
                                );
                                for i in 0..2 {
                                    accumulator[index][i].add_assign(&value[i]);
                                }
                            }
                        },
                    );
                } else {
                    assert_eq!(sources.extension_field_inputs.len(), IN);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
                    let challenges = batch_challenges.as_array().unwrap_unchecked();

                    apply_row_wise::<F, _>(
                        vec![],
                        vec![accumulator],
                        work_size,
                        worker,
                        |_, mut ext_dest, chunk_start, chunk_size| {
                            assert_eq!(ext_dest.len(), 1);
                            let accumulator = ext_dest.pop().unwrap();
                            for index in 0..chunk_size {
                                let absolute_index = chunk_start + index;
                                let value =
                                    kernel.evaluate::<_, false>(absolute_index, inputs, challenges);
                                for i in 0..2 {
                                    accumulator[index][i].add_assign(&value[i]);
                                }
                            }
                        },
                    );
                }
            }
            i if i + 1 == total_sumcheck_rounds => {
                assert!(i >= 3);

                let sources =
                    storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
                {
                    assert!(sources.base_field_inputs.is_empty());
                    assert_eq!(sources.extension_field_inputs.len(), IN);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
                    let challenges = batch_challenges.as_array().unwrap_unchecked();

                    apply_row_wise::<F, _>(
                        vec![],
                        vec![accumulator],
                        work_size,
                        worker,
                        |_, mut ext_dest, chunk_start, chunk_size| {
                            assert_eq!(ext_dest.len(), 1);
                            let accumulator = ext_dest.pop().unwrap();
                            for index in 0..chunk_size {
                                let absolute_index = chunk_start + index;
                                let value =
                                    kernel.evaluate::<_, true>(absolute_index, inputs, challenges);
                                for i in 0..2 {
                                    accumulator[index][i].add_assign(&value[i]);
                                }
                            }
                        },
                    );
                }

                // Fill the storage
                sources.collect_last_values(inputs, last_evaluations);
            }
            1.. => {
                let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
                {
                    assert!(sources.base_field_inputs.is_empty());
                    assert_eq!(sources.extension_field_inputs.len(), IN);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
                    let challenges = batch_challenges.as_array().unwrap_unchecked();

                    apply_row_wise::<F, _>(
                        vec![],
                        vec![accumulator],
                        work_size,
                        worker,
                        |_, mut ext_dest, chunk_start, chunk_size| {
                            assert_eq!(ext_dest.len(), 1);
                            let accumulator = ext_dest.pop().unwrap();
                            for index in 0..chunk_size {
                                let absolute_index = chunk_start + index;
                                let value =
                                    kernel.evaluate::<_, false>(absolute_index, inputs, challenges);
                                for i in 0..2 {
                                    accumulator[index][i].add_assign(&value[i]);
                                }
                            }
                        },
                    );
                }
            }
        }
    }
}
