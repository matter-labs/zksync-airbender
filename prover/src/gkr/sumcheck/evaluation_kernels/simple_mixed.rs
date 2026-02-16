use crate::gkr::{
    prover::{apply_row_wise, split_destinations},
    sumcheck::access_and_fold::ExtensionFieldPoly,
};

use super::*;
use std::mem::MaybeUninit;

// Trait for kernels that can take both base field and extension field as inputs,
// but always output values in extension

pub trait MixedFieldsInOutFixedSizesEvaluationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
>: Send + Sync
{
    #[inline(always)]
    fn evaluate_forward<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; IN_BASE],
        ext_sources: &[SE; IN_EXT],
    ) -> [E; OUT] {
        assert!(IN_BASE + IN_EXT > 0);
        assert!(OUT > 0);
        let sources = sources.each_ref().map(|el| el.get_at_index(index));
        let ext_sources = ext_sources.each_ref().map(|el| el.get_at_index(index));
        let eval = self.pointwise_eval_forward(&sources, &ext_sources);

        eval
    }

    #[inline(always)]
    fn evaluate_first_round<
        SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    >(
        &self,
        index: usize,
        sources: &[SB; IN_BASE],
        ext_sources: &[SE; IN_EXT],
        output_sources: &[SOUT; OUT],
        batch_challenges: &[E; OUT],
    ) -> [E; 2] {
        assert!(IN_BASE + IN_EXT > 0);
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
                let ctx = sources.get_unchecked(0).get_collapse_context();

                let sources = sources.each_ref().map(|el| el.get_f1_minus_f0_only(index));
                let ext_sources = ext_sources
                    .each_ref()
                    .map(|el| el.get_f1_minus_f0_only(index));
                let evals = self.pointwise_eval(&sources, &ext_sources, ctx);
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
        RB: EvaluationRepresentation<F, E>,
        SB: EvaluationFormStorage<F, E, RB>,
        SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[SB; IN_BASE],
        ext_sources: &[SE; IN_EXT],
        batch_challenges: &[E; OUT],
    ) -> [E; 2] {
        assert!(IN_BASE + IN_EXT > 0);
        assert!(OUT > 0);
        unsafe {
            let ctx = sources.get_unchecked(0).get_collapse_context();

            let mut result = [const { MaybeUninit::uninit() }; 2];
            let mut p0s = [const { MaybeUninit::uninit() }; IN_BASE];
            let mut p1s = [const { MaybeUninit::uninit() }; IN_BASE];
            for i in 0..IN_BASE {
                let [f0, f1] = sources[i].get_two_points::<EXPLICIT_FORM>(index);
                p0s[i].write(f0);
                p1s[i].write(f1);
            }
            let p0s = p0s.map(|el| el.assume_init());
            let p1s = p1s.map(|el| el.assume_init());

            let mut ext_p0s = [const { MaybeUninit::uninit() }; IN_EXT];
            let mut ext_p1s = [const { MaybeUninit::uninit() }; IN_EXT];
            for i in 0..IN_EXT {
                let [f0, f1] = ext_sources[i].get_two_points::<EXPLICIT_FORM>(index);
                ext_p0s[i].write(f0);
                ext_p1s[i].write(f1);
            }
            let ext_p0s = ext_p0s.map(|el| el.assume_init());
            let ext_p1s = ext_p1s.map(|el| el.assume_init());

            for (j, (p_b, p_ext)) in [(&p0s, &ext_p0s), (&p1s, &ext_p1s)].into_iter().enumerate() {
                let evals = self.pointwise_eval(p_b, p_ext, ctx);
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

    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; IN_BASE],
        ext_input: &[ExtensionFieldRepresentation<F, E>; IN_EXT],
        ctx: &RB::CollapseContext,
    ) -> [E; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(
        &self,
        input: &[BaseFieldRepresentation<F>; IN_BASE],
        ext_input: &[ExtensionFieldRepresentation<F, E>; IN_EXT],
    ) -> [E; OUT] {
        self.pointwise_eval(input, ext_input, &())
    }
}

#[inline(always)]
fn evaluate_mixed_field_in_out_fixed_sizes_evaluation_kernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
    K: MixedFieldsInOutFixedSizesEvaluationKernel<F, E, IN_BASE, IN_EXT, OUT>,
    RB: EvaluationRepresentation<F, E>,
    SB: EvaluationFormStorage<F, E, RB>,
    SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    const EXPLICIT_FORM: bool,
>(
    kernel: &K,
    index: usize,
    sources: &[SB],
    ext_sources: &[SE],
    batch_challenges: &[E],
) -> [E; 2] {
    debug_assert_eq!(sources.len(), IN_BASE);
    debug_assert_eq!(ext_sources.len(), IN_EXT);
    debug_assert_eq!(batch_challenges.len(), OUT);
    unsafe {
        let inputs = sources.as_array().unwrap_unchecked();
        let inputs_ext = ext_sources.as_array().unwrap_unchecked();
        let challenges = batch_challenges.as_array().unwrap_unchecked();
        K::evaluate::<RB, SB, SE, EXPLICIT_FORM>(kernel, index, inputs, inputs_ext, challenges)
    }
}

#[inline(always)]
fn evaluate_mixed_field_in_out_fixed_sizes_evaluation_kernel_first_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
    K: MixedFieldsInOutFixedSizesEvaluationKernel<F, E, IN_BASE, IN_EXT, OUT>,
    SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
    SE: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
    SOUT: EvaluationFormStorage<F, E, ExtensionFieldRepresentation<F, E>>,
>(
    kernel: &K,
    index: usize,
    sources: &[SB],
    ext_sources: &[SE],
    outputs: &[SOUT],
    batch_challenges: &[E],
) -> [E; 2] {
    debug_assert_eq!(sources.len(), IN_BASE);
    debug_assert_eq!(ext_sources.len(), IN_EXT);
    debug_assert_eq!(outputs.len(), OUT);
    debug_assert_eq!(batch_challenges.len(), OUT);
    unsafe {
        let inputs = sources.as_array().unwrap_unchecked();
        let inputs_ext = ext_sources.as_array().unwrap_unchecked();
        let outputs = outputs.as_array().unwrap_unchecked();
        let challenges = batch_challenges.as_array().unwrap_unchecked();
        K::evaluate_first_round::<SB, SE, SOUT>(
            kernel, index, inputs, inputs_ext, outputs, challenges,
        )
    }
}

pub fn forward_evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
    K: MixedFieldsInOutFixedSizesEvaluationKernel<F, E, IN_BASE, IN_EXT, OUT>,
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

        let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();

        let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();

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
                    let value = kernel.evaluate_forward(absolute_index, inputs, ext_inputs);
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

pub fn evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
    K: MixedFieldsInOutFixedSizesEvaluationKernel<F, E, IN_BASE, IN_EXT, OUT>,
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
    assert!(total_sumcheck_rounds >= 4);
    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());
    unsafe {
        match step {
            0 => {
                let sources = storage.get_for_sumcheck_round_0(inputs);
                assert!(sources.base_field_outputs.is_empty());
                if sources.extension_field_outputs.is_empty() == false {
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(sources.extension_field_outputs.len(), OUT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                    ext_inputs,
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
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                let value = kernel.evaluate::<_, _, _, false>(
                                    absolute_index,
                                    inputs,
                                    ext_inputs,
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
            1 => {
                let sources = storage.get_for_sumcheck_round_1(inputs, folding_challenges);
                {
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                let value = kernel.evaluate::<_, _, _, false>(
                                    absolute_index,
                                    inputs,
                                    ext_inputs,
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
            2 => {
                let sources = storage.get_for_sumcheck_round_2(inputs, folding_challenges);
                {
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                let value = kernel.evaluate::<_, _, _, false>(
                                    absolute_index,
                                    inputs,
                                    ext_inputs,
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
                assert!(i >= 3);
                let sources =
                    storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
                {
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                let value = kernel.evaluate::<_, _, _, true>(
                                    absolute_index,
                                    inputs,
                                    ext_inputs,
                                    challenges,
                                );
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
            3.. => {
                let sources =
                    storage.get_for_sumcheck_round_3_and_beyond(inputs, folding_challenges);
                {
                    assert_eq!(sources.base_field_inputs.len(), IN_BASE);
                    assert_eq!(sources.extension_field_inputs.len(), IN_EXT);
                    assert_eq!(batch_challenges.len(), OUT);

                    let inputs = sources.base_field_inputs.as_array().unwrap_unchecked();
                    let ext_inputs = sources.extension_field_inputs.as_array().unwrap_unchecked();
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
                                let value = kernel.evaluate::<_, _, _, false>(
                                    absolute_index,
                                    inputs,
                                    ext_inputs,
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
