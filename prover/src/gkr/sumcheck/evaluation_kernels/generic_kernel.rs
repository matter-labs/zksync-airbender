use super::*;
use crate::gkr::prover::apply_row_wise;
use crate::gkr::prover::split_destinations;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPolySource;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct GKRInputs {
    pub inputs_in_base: Vec<GKRAddress>,
    pub inputs_in_extension: Vec<GKRAddress>,
    pub outputs_in_base: Vec<GKRAddress>,
    pub outputs_in_extension: Vec<GKRAddress>,
}

pub trait BatchedGKRKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    fn num_challenges(&self) -> usize;
    fn get_inputs(&self) -> GKRInputs;
    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        input_trace_len: usize,
        worker: &Worker,
    );
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
    );
}

pub fn forward_evaluate_single_input_kernel_with_base_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    K: SingleInputTypeBatchSumcheckEvaluationKernel<F, E>,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    unreachable!();

    // assert!(trace_len.is_power_of_two());
    // use crate::gkr::prover::apply_row_wise;
    // unsafe {
    //     let mut inputs = inputs.clone();
    //     let outputs = std::mem::replace(&mut inputs.outputs_in_extension, vec![]);
    //     for output in outputs.iter() {
    //         output.assert_as_layer(expected_output_layer);
    //     }
    //     let sources = storage.get_for_sumcheck_round_0(&inputs);
    //     let mut destinations = Vec::with_capacity(outputs.len());
    //     for _ in 0..outputs.len() {
    //         destinations.push(Box::<[E]>::new_uninit_slice(trace_len));
    //     }
    //     let mut destinations_refs = Vec::with_capacity(outputs.len());
    //     for el in destinations.iter_mut() {
    //         destinations_refs.push(&mut el[..]);
    //     }

    //     let inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();

    //     apply_row_wise::<F, _>(
    //         vec![],
    //         destinations_refs,
    //         trace_len,
    //         worker,
    //         |_, ext_dest, chunk_start, chunk_size| {
    //             let mut destinations: [&mut [MaybeUninit<E>]; OUT] = ext_dest.try_into().unwrap();
    //             for index in 0..chunk_size {
    //                 let absolute_index = chunk_start + index;
    //                 let value = kernel.evaluate_forward(absolute_index, inputs);
    //                 for (dst, val) in destinations.iter_mut().zip(value.into_iter()) {
    //                     dst[index].write(val);
    //                 }
    //             }
    //         },
    //     );

    //     for (output, destination) in outputs.into_iter().zip(destinations.into_iter()) {
    //         let values = destination.assume_init();
    //         storage.insert_extension_at_layer(
    //             expected_output_layer,
    //             output,
    //             ExtensionFieldPoly::new(values),
    //         );
    //     }
    // }
}

pub fn evaluate_single_input_kernel_with_base_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    K: SingleInputTypeBatchSumcheckEvaluationKernel<F, E>,
    const N: usize,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    step: usize,
    challenges: &[E],
    folding_challenges: &[E],
    accumulator: &mut [[E; 2]],
    total_sumcheck_rounds: usize,
    last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
    worker: &Worker,
) {
    assert_eq!(challenges.len(), kernel.num_challenges());

    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());
    match step {
        0 => {
            let sources = storage.get_for_sumcheck_round_0(inputs);
            let inputs = &sources.base_field_inputs;
            assert!(sources.extension_field_inputs.is_empty());
            if sources.base_field_outputs.is_empty() == false {
                let outputs = &sources.base_field_outputs;
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
                                &(),
                            );
                            for i in 0..2 {
                                accumulator[index][i].add_assign(&value[i]);
                            }
                        }
                    },
                );
            } else if sources.extension_field_outputs.is_empty() == false {
                let outputs = &sources.extension_field_outputs;
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
                                &(),
                            );
                            for i in 0..2 {
                                accumulator[index][i].add_assign(&value[i]);
                            }
                        }
                    },
                );
            } else {
                let outputs: &[BaseFieldPolySource<F>] = &[][..];
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
                                &(),
                            );
                            for i in 0..2 {
                                accumulator[index][i].add_assign(&value[i]);
                            }
                        }
                    },
                );
            }
        }
        1 => {
            let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
            let inputs = &sources.base_field_inputs;
            assert!(sources.extension_field_inputs.is_empty());
            apply_row_wise::<F, _>(
                vec![],
                vec![accumulator],
                work_size,
                worker,
                |_, mut ext_dest, chunk_start, chunk_size| {
                    assert_eq!(ext_dest.len(), 1);
                    let accumulator = ext_dest.pop().unwrap();
                    let ctx = inputs[0].get_collapse_context();
                    for index in 0..chunk_size {
                        let absolute_index = chunk_start + index;
                        let value =
                            kernel.evaluate::<_, _, false>(absolute_index, inputs, challenges, ctx);
                        for i in 0..2 {
                            accumulator[index][i].add_assign(&value[i]);
                        }
                    }
                },
            );
        }
        2 => {
            let sources = storage.get_for_sumcheck_round_2(inputs, folding_challenges);
            let inputs = &sources.base_field_inputs;
            assert!(sources.extension_field_inputs.is_empty());
            apply_row_wise::<F, _>(
                vec![],
                vec![accumulator],
                work_size,
                worker,
                |_, mut ext_dest, chunk_start, chunk_size| {
                    assert_eq!(ext_dest.len(), 1);
                    let accumulator = ext_dest.pop().unwrap();
                    let ctx = inputs[0].get_collapse_context();
                    for index in 0..chunk_size {
                        let absolute_index = chunk_start + index;
                        let value =
                            kernel.evaluate::<_, _, false>(absolute_index, inputs, challenges, ctx);
                        for i in 0..2 {
                            accumulator[index][i].add_assign(&value[i]);
                        }
                    }
                },
            );
        }
        i if i + 1 == total_sumcheck_rounds => {
            assert!(i >= 3);

            let sources = storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
            {
                let inputs = &sources.base_field_inputs;
                assert!(sources.extension_field_inputs.is_empty());
                apply_row_wise::<F, _>(
                    vec![],
                    vec![accumulator],
                    work_size,
                    worker,
                    |_, mut ext_dest, chunk_start, chunk_size| {
                        assert_eq!(ext_dest.len(), 1);
                        let accumulator = ext_dest.pop().unwrap();
                        let ctx = inputs[0].get_collapse_context();
                        for index in 0..chunk_size {
                            let absolute_index = chunk_start + index;
                            let value = kernel.evaluate::<_, _, true>(
                                absolute_index,
                                inputs,
                                challenges,
                                ctx,
                            );
                            for i in 0..2 {
                                accumulator[index][i].add_assign(&value[i]);
                            }
                        }
                    },
                );
            }

            sources.collect_last_values(inputs, last_evaluations);
        }
        3.. => {
            let sources = storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
            let inputs = &sources.base_field_inputs;
            assert!(sources.extension_field_inputs.is_empty());
            apply_row_wise::<F, _>(
                vec![],
                vec![accumulator],
                work_size,
                worker,
                |_, mut ext_dest, chunk_start, chunk_size| {
                    assert_eq!(ext_dest.len(), 1);
                    let accumulator = ext_dest.pop().unwrap();
                    let ctx = inputs[0].get_collapse_context();
                    for index in 0..chunk_size {
                        let absolute_index = chunk_start + index;
                        let value =
                            kernel.evaluate::<_, _, false>(absolute_index, inputs, challenges, ctx);
                        for i in 0..2 {
                            accumulator[index][i].add_assign(&value[i]);
                        }
                    }
                },
            );
        }
    }
}

pub fn evaluate_single_input_kernel_with_extension_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    K: SingleInputTypeBatchSumcheckEvaluationKernel<F, E>,
>(
    kernel: &K,
    inputs: &GKRInputs,
    storage: &mut GKRStorage<F, E>,
    step: usize,
    batch_challenges: &[E],
    folding_challenges: &[E],
    accumulator: &mut [[E; 2]],
    total_sumcheck_rounds: usize,
    last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
    worker: &Worker,
) {
    unreachable!();

    // let work_size = accumulator.len();
    // assert!(work_size.is_power_of_two());
    // let mut accumulator_chunks =
    //     split_destinations(vec![accumulator], worker.get_geometry(work_size));
    // match step {
    //     0 => {
    //         let sources = storage.get_for_sumcheck_round_0(inputs);
    //         assert!(sources.base_field_inputs.is_empty());
    //         assert!(sources.base_field_outputs.is_empty());
    //         if sources.extension_field_outputs.is_empty() == false {
    //             for index in 0..accumulator.len() {
    //                 let value = kernel.evaluate_first_round(
    //                     index,
    //                     &sources.extension_field_inputs,
    //                     &sources.extension_field_outputs,
    //                     batch_challenges,
    //                 );
    //                 for i in 0..2 {
    //                     accumulator[index][i].add_assign(&value[i]);
    //                 }
    //             }
    //         } else {
    //             for index in 0..accumulator.len() {
    //                 let value = kernel.evaluate::<_, _, false>(
    //                     index,
    //                     &sources.extension_field_inputs,
    //                     batch_challenges,
    //                 );
    //                 for i in 0..2 {
    //                     accumulator[index][i].add_assign(&value[i]);
    //                 }
    //             }
    //         }
    //         // for input in sources.extension_field_inputs.iter() {
    //         //     dbg!(input.current_values());
    //         // }
    //         // for output in sources.extension_field_outputs.iter() {
    //         //     dbg!(output.current_values());
    //         // }
    //     }
    //     i if i + 1 == total_sumcheck_rounds => {
    //         assert!(i >= 3);

    //         let sources = storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
    //         assert!(sources.base_field_inputs.is_empty());
    //         for index in 0..accumulator.len() {
    //             let value = kernel.evaluate::<_, _, true>(
    //                 index,
    //                 &sources.extension_field_inputs,
    //                 batch_challenges,
    //             );
    //             for i in 0..2 {
    //                 accumulator[index][i].add_assign(&value[i]);
    //             }
    //         }

    //         for source in sources.extension_field_inputs.iter() {
    //             dbg!(source.current_values());
    //         }

    //         // Fill the storage
    //         sources.collect_last_values(inputs, last_evaluations);
    //     }
    //     1.. => {
    //         let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
    //         assert!(sources.base_field_inputs.is_empty());
    //         for index in 0..accumulator.len() {
    //             let value = kernel.evaluate::<_, _, false>(
    //                 index,
    //                 &sources.extension_field_inputs,
    //                 batch_challenges,
    //             );
    //             for i in 0..2 {
    //                 accumulator[index][i].add_assign(&value[i]);
    //             }
    //         }
    //         for source in sources.extension_field_inputs.iter() {
    //             dbg!(source.previous_values());
    //             dbg!(source.current_values());
    //         }
    //     }
    // }
}
