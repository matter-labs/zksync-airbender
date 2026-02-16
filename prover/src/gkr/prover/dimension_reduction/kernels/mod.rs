use super::*;
use crate::gkr::sumcheck::access_and_fold::*;
use std::mem::MaybeUninit;

pub mod logup;
pub mod pairwise_product;

// Such kernels assume that for pairwise dimension reduction "fixed" index variable encodes LSB.
// In their essence the access pattern is always as
// p_next(X) = \sum eq(Y, X) max_quadratic_fn(p(Y, 0), p(Y, 1), q(Y, 0), q(Y, 1))
pub trait DimensionReducingEvaluationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
>: Send + Sync
{
    #[inline(always)]
    fn evaluate_forward<S: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>>(
        &self,
        index: usize,
        sources: &[S; IN],
    ) -> [E; OUT] {
        debug_assert_eq!(index % 2, 0);
        assert!(IN > 0);
        assert!(OUT > 0);
        let pairwise_index = index + 1;
        let a = std::array::from_fn(|i| sources[i].get_at_index(index));
        let b = std::array::from_fn(|i| sources[i].get_at_index(pairwise_index));
        let eval = self.pointwise_eval_forward(&a, &b);

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
        debug_assert_eq!(index % 2, 0);
        assert!(IN > 0);
        assert!(OUT > 0);
        let pairwise_index = index + 1;
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
                let a = sources.each_ref().map(|el| el.get_f1_minus_f0_only(index));
                let b = sources
                    .each_ref()
                    .map(|el| el.get_f1_minus_f0_only(pairwise_index));
                let evals = self.pointwise_eval(&a, &b);
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
        debug_assert_eq!(index % 2, 0);
        assert!(IN > 0);
        assert!(OUT > 0);
        let pairwise_index = index + 1;
        unsafe {
            let mut result = [const { MaybeUninit::uninit() }; 2];
            let mut a0s = [const { MaybeUninit::uninit() }; IN];
            let mut a1s = [const { MaybeUninit::uninit() }; IN];
            for i in 0..IN {
                let [f0, f1] = sources[i].get_two_points::<EXPLICIT_FORM>(index);
                a0s[i].write(f0);
                a1s[i].write(f1);
            }
            let a0s = a0s.map(|el| el.assume_init());
            let a1s = a1s.map(|el| el.assume_init());

            let mut b0s = [const { MaybeUninit::uninit() }; IN];
            let mut b1s = [const { MaybeUninit::uninit() }; IN];
            for i in 0..IN {
                let [f0, f1] = sources[i].get_two_points::<EXPLICIT_FORM>(pairwise_index);
                b0s[i].write(f0);
                b1s[i].write(f1);
            }
            let b0s = b0s.map(|el| el.assume_init());
            let b1s = b1s.map(|el| el.assume_init());

            for (j, (a, b)) in [(&a0s, &b0s), (&a1s, &b1s)].into_iter().enumerate() {
                let evals = self.pointwise_eval(a, b);
                let mut eval = batch_challenges[0];
                eval.mul_assign(&evals[0]);
                for i in 1..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign(&evals[i]);
                    eval.add_assign(&t);
                }
                result[j].write(eval);
            }

            result.map(|el| el.assume_init())
        }
    }

    fn pointwise_eval(
        &self,
        a: &[ExtensionFieldRepresentation<F, E>; IN],
        b: &[ExtensionFieldRepresentation<F, E>; IN],
    ) -> [E; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(
        &self,
        a: &[ExtensionFieldRepresentation<F, E>; IN],
        b: &[ExtensionFieldRepresentation<F, E>; IN],
    ) -> [E; OUT] {
        self.pointwise_eval(a, b)
    }
}

pub fn forward_evaluate_dimension_reducing_kernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: DimensionReducingEvaluationKernel<F, E, IN, OUT>,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    input_trace_len: usize,
    worker: &Worker,
) {
    assert!(input_trace_len.is_power_of_two());
    let output_trace_len = input_trace_len / 2;
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
            destinations.push(Box::<[E]>::new_uninit_slice(output_trace_len));
        }
        let mut destinations_refs = Vec::with_capacity(outputs.len());
        for el in destinations.iter_mut() {
            destinations_refs.push(&mut el[..]);
        }

        let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();

        apply_row_wise::<F, _>(
            vec![],
            destinations_refs,
            output_trace_len,
            worker,
            |_, ext_dest, chunk_start, chunk_size| {
                assert_eq!(ext_dest.len(), OUT);
                let mut destinations: [&mut [MaybeUninit<E>]; OUT] = ext_dest.try_into().unwrap();
                for index in 0..chunk_size {
                    let absolute_index = chunk_start + index;
                    let value = kernel.evaluate_forward(absolute_index * 2, inputs);
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

pub fn evaluate_single_dimension_reducing_kernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: DimensionReducingEvaluationKernel<F, E, IN, OUT>,
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

                    // self-check the sizes
                    for el in inputs.iter() {
                        assert_eq!(work_size * 2, el.next_layer_size);
                    }
                    for el in outputs.iter() {
                        assert_eq!(work_size, el.next_layer_size);
                    }

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
                                    absolute_index * 2,
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
                    for el in inputs.iter() {
                        assert_eq!(work_size * 2, el.next_layer_size);
                    }

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
                                let value = kernel.evaluate::<_, false>(
                                    absolute_index * 2,
                                    inputs,
                                    challenges,
                                );
                                for i in 0..2 {
                                    accumulator[index][i].add_assign(&value[i]);
                                }
                            }
                        },
                    );
                }
            }
            i if i + 1 == total_sumcheck_rounds => {
                assert!(i >= 1);

                let sources =
                    storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
                {
                    assert!(sources.base_field_inputs.is_empty());
                    assert_eq!(sources.extension_field_inputs.len(), IN);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
                    let challenges = batch_challenges.as_array().unwrap_unchecked();

                    for el in inputs.iter() {
                        assert_eq!(work_size * 2, el.next_layer_size);
                    }

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

                    for el in inputs.iter() {
                        assert_eq!(work_size * 2, el.next_layer_size);
                    }

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
                                let value = kernel.evaluate::<_, false>(
                                    absolute_index * 2,
                                    inputs,
                                    challenges,
                                );
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
