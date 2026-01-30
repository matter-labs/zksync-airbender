use crate::gkr::prover::split_destinations;

use super::*;

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
        trace_len: usize,
        worker: &Worker,
    );
    fn evaluate_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        batch_challenges: &[E],
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    );
}

pub fn evaluate_single_input_kernel_with_base_inputs<
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
    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());
    let mut accumulator_chunks =
        split_destinations(vec![accumulator], worker.get_geometry(work_size));
    match step {
        0 => {
            let sources = storage.get_for_sumcheck_round_0(inputs);
            assert!(sources.extension_field_inputs.is_empty());
            if sources.base_field_outputs.is_empty() == false {
                for index in 0..accumulator.len() {
                    let value = kernel.evaluate_first_round(
                        index,
                        &sources.base_field_inputs,
                        &sources.base_field_outputs,
                        batch_challenges,
                    );
                    for i in 0..2 {
                        accumulator[index][i].add_assign(&value[i]);
                    }
                }
            } else if sources.extension_field_outputs.is_empty() == false {
                for index in 0..accumulator.len() {
                    let value = kernel.evaluate_first_round(
                        index,
                        &sources.base_field_inputs,
                        &sources.extension_field_outputs,
                        batch_challenges,
                    );
                    for i in 0..2 {
                        accumulator[index][i].add_assign(&value[i]);
                    }
                }
            } else {
                for index in 0..accumulator.len() {
                    let value = kernel.evaluate::<_, _, false>(
                        index,
                        &sources.base_field_inputs,
                        batch_challenges,
                    );
                    for i in 0..2 {
                        accumulator[index][i].add_assign(&value[i]);
                    }
                }
            }
        }
        i if i + 1 == total_sumcheck_rounds => {
            todo!();
        }
        1 => {
            let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
            assert!(sources.base_field_inputs.is_empty());
            for index in 0..accumulator.len() {
                let value = kernel.evaluate::<_, _, false>(
                    index,
                    &sources.base_field_inputs,
                    batch_challenges,
                );
                for i in 0..2 {
                    accumulator[index][i].add_assign(&value[i]);
                }
            }
        }
        2 => {
            todo!()
        }
        3.. => {
            todo!()
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
    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());
    let mut accumulator_chunks =
        split_destinations(vec![accumulator], worker.get_geometry(work_size));
    match step {
        0 => {
            let sources = storage.get_for_sumcheck_round_0(inputs);
            assert!(sources.base_field_inputs.is_empty());
            assert!(sources.base_field_outputs.is_empty());
            if sources.extension_field_outputs.is_empty() == false {
                for index in 0..accumulator.len() {
                    let value = kernel.evaluate_first_round(
                        index,
                        &sources.extension_field_inputs,
                        &sources.extension_field_outputs,
                        batch_challenges,
                    );
                    for i in 0..2 {
                        accumulator[index][i].add_assign(&value[i]);
                    }
                }
            } else {
                for index in 0..accumulator.len() {
                    let value = kernel.evaluate::<_, _, false>(
                        index,
                        &sources.extension_field_inputs,
                        batch_challenges,
                    );
                    for i in 0..2 {
                        accumulator[index][i].add_assign(&value[i]);
                    }
                }
            }
            // for input in sources.extension_field_inputs.iter() {
            //     dbg!(input.current_values());
            // }
            // for output in sources.extension_field_outputs.iter() {
            //     dbg!(output.current_values());
            // }
        }
        i if i + 1 == total_sumcheck_rounds => {
            let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
            assert!(sources.base_field_inputs.is_empty());
            for index in 0..accumulator.len() {
                let value = kernel.evaluate::<_, _, true>(
                    index,
                    &sources.extension_field_inputs,
                    batch_challenges,
                );
                for i in 0..2 {
                    accumulator[index][i].add_assign(&value[i]);
                }
            }
            println!("COLLECTING LAST LAYER VALUES");

            for source in sources.extension_field_inputs.iter() {
                dbg!(source.current_values());
            }

            // Fill the storage
            sources.collect_last_values(inputs, last_evaluations);
        }
        1.. => {
            let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
            assert!(sources.base_field_inputs.is_empty());
            for index in 0..accumulator.len() {
                let value = kernel.evaluate::<_, _, false>(
                    index,
                    &sources.extension_field_inputs,
                    batch_challenges,
                );
                for i in 0..2 {
                    accumulator[index][i].add_assign(&value[i]);
                }
            }
            for source in sources.extension_field_inputs.iter() {
                dbg!(source.previous_values());
                dbg!(source.current_values());
            }
        }
    }
}
