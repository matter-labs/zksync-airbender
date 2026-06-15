use crate::gkr::PAR_THRESHOLD;

use super::*;

pub mod in_3_out_1;
pub mod in_3_out_3;

pub trait TransitionRoundImplementation<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Send + Sync
{
    const INPUT_WINDOW_SIZE: usize;
    const OUTPUT_WINDOW_SIZE: usize;
    type AccumulatorOutput: 'static + Clone + Copy + Send + Sync;
    type FoldingPrefix: Sync;
    type PerPolyScratch: 'static + Clone + Copy;
    type EvaluationScratch: 'static + Clone + Copy;

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize;
    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize;

    fn make_prefix_from_all_folding_challenges(
        folding_challenges: &[E],
        worker: &Worker,
    ) -> Self::FoldingPrefix;

    fn make_accumulation_output() -> Self::AccumulatorOutput;
    fn reduce_accumulators(accs: Vec<Self::AccumulatorOutput>) -> Self::AccumulatorOutput;
    fn make_poly_scratch() -> Self::PerPolyScratch;
    fn make_evaluation_scratch() -> Self::EvaluationScratch;
    fn clear_evaluation_scratch(scratch: &mut Self::EvaluationScratch);

    fn read_then_fold_and_interpolate_base(
        dst: &mut Self::PerPolyScratch,
        src: &DisjointAccessQuasiSlice<F, false>,
        buffer: &mut DisjointAccessQuasiSlice<E, true>,
        prefix: &Self::FoldingPrefix,
        input_size: usize,
        row: usize,
    );

    fn read_then_fold_base_without_interpolation(
        dst: &mut Self::PerPolyScratch,
        src: &DisjointAccessQuasiSlice<F, false>,
        buffer: &mut DisjointAccessQuasiSlice<E, true>,
        prefix: &Self::FoldingPrefix,
        input_size: usize,
        row: usize,
    );

    fn read_then_fold_and_interpolate_ext(
        dst: &mut Self::PerPolyScratch,
        src: &DisjointAccessQuasiSlice<E, false>,
        buffer: &mut DisjointAccessQuasiSlice<E, true>,
        prefix: &Self::FoldingPrefix,
        input_size: usize,
        row: usize,
    );

    fn read_then_fold_ext_without_interpolation(
        dst: &mut Self::PerPolyScratch,
        src: &DisjointAccessQuasiSlice<E, false>,
        buffer: &mut DisjointAccessQuasiSlice<E, true>,
        prefix: &Self::FoldingPrefix,
        input_size: usize,
        row: usize,
    );

    fn evaluate_quadratic(
        dst: &mut Self::EvaluationScratch,
        a: &Self::PerPolyScratch,
        b: &Self::PerPolyScratch,
        coeff: &E,
    );
    fn evaluate_linear(dst: &mut Self::EvaluationScratch, a: &Self::PerPolyScratch, coeff: &E);
    fn apply_additive_constant(dst: &mut Self::EvaluationScratch, coeff: &E);
    fn apply_eq_suffix(
        dst: &mut Self::AccumulatorOutput,
        src: &Self::EvaluationScratch,
        suffix: &E,
    );
}

pub fn evaluate_transition_with_full_sized_scratch_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: TransitionRoundImplementation<F, E>,
>(
    base_field_inputs: Vec<DisjointAccessQuasiSlice<F, false>>,
    ext_field_inputs: Vec<DisjointAccessQuasiSlice<E, false>>,
    base_field_folding_outputs: Vec<DisjointAccessQuasiSlice<E, true>>,
    ext_field_folding_outputs: Vec<DisjointAccessQuasiSlice<E, true>>,
    description: &BatchEvaluationCompactDescription<F, E>,
    precomputed_eq_prefix: &I::FoldingPrefix,
    precomputed_eq_suffix: &[E],
    unfolded_input_size_log2: usize,
    worker: &Worker,
) -> I::AccumulatorOutput {
    assert!(unfolded_input_size_log2 >= 4);
    let work_size = I::work_size_for_unfolded_input_size(unfolded_input_size_log2);
    assert_eq!(precomputed_eq_suffix.len(), work_size);

    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut acc_chunks = vec![I::make_accumulation_output(); geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);

            let base_field_inputs = base_field_inputs.clone();
            let ext_field_inputs = ext_field_inputs.clone();
            let mut base_field_folding_outputs = base_field_folding_outputs.clone();
            let mut ext_field_folding_outputs = ext_field_folding_outputs.clone();
            let acc_dst = it.next().expect("dst chunk");

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                *acc_dst = evaluate_transition_with_full_sized_scratch::<F, E, I>(
                    &base_field_inputs,
                    &ext_field_inputs,
                    &mut base_field_folding_outputs,
                    &mut ext_field_folding_outputs,
                    description,
                    precomputed_eq_prefix,
                    precomputed_eq_suffix,
                    unfolded_input_size_log2,
                    chunk_start..(chunk_start + chunk_size),
                );
            })
        }
    });

    I::reduce_accumulators(acc_chunks)
}

pub fn evaluate_transition_with_full_sized_scratch<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: TransitionRoundImplementation<F, E>,
>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_field_folding_outputs: &mut [DisjointAccessQuasiSlice<E, true>],
    ext_field_folding_outputs: &mut [DisjointAccessQuasiSlice<E, true>],
    description: &BatchEvaluationCompactDescription<F, E>,
    precomputed_eq_prefix: &I::FoldingPrefix,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    row_range: core::ops::Range<usize>,
) -> I::AccumulatorOutput {
    assert!(input_size_log2 >= 4);

    let mut accumulator = I::make_accumulation_output();

    assert_eq!(
        description.base_read_with_interpolation.len(),
        base_field_inputs.len()
    );
    assert_eq!(
        description.ext_read_with_interpolation.len(),
        ext_field_inputs.len()
    );

    assert_eq!(base_field_inputs.len(), base_field_folding_outputs.len());
    assert_eq!(ext_field_inputs.len(), ext_field_folding_outputs.len());

    let input_size = 1 << input_size_log2;

    let mut field_scratch = vec![
        I::make_poly_scratch();
        description.base_read_with_interpolation.len()
            + description.ext_read_with_interpolation.len()
    ]
    .into_boxed_slice();
    let mut eval_scratch = I::make_evaluation_scratch();

    for row in row_range {
        let eq_prefactor = &precomputed_eq_suffix[row];
        I::clear_evaluation_scratch(&mut eval_scratch);

        // first we read everything

        for (((dst, src), interpolate_at_inf), buffer) in field_scratch
            [..base_field_folding_outputs.len()]
            .iter_mut()
            .zip(base_field_inputs.iter())
            .zip(description.base_read_with_interpolation.iter())
            .zip(base_field_folding_outputs.iter_mut())
        {
            if *interpolate_at_inf {
                I::read_then_fold_and_interpolate_base(
                    dst,
                    src,
                    buffer,
                    precomputed_eq_prefix,
                    input_size,
                    row,
                );
            } else {
                I::read_then_fold_base_without_interpolation(
                    dst,
                    src,
                    buffer,
                    precomputed_eq_prefix,
                    input_size,
                    row,
                );
            }
        }

        for (((dst, src), interpolate_at_inf), buffer) in field_scratch
            [base_field_folding_outputs.len()..]
            .iter_mut()
            .zip(ext_field_inputs.iter())
            .zip(description.ext_read_with_interpolation.iter())
            .zip(ext_field_folding_outputs.iter_mut())
        {
            if *interpolate_at_inf {
                I::read_then_fold_and_interpolate_ext(
                    dst,
                    src,
                    buffer,
                    precomputed_eq_prefix,
                    input_size,
                    row,
                );
            } else {
                I::read_then_fold_ext_without_interpolation(
                    dst,
                    src,
                    buffer,
                    precomputed_eq_prefix,
                    input_size,
                    row,
                );
            }
        }

        // and now compute
        for step in description.folded_evaluation_steps.iter() {
            match *step {
                FoldedEvaluationStep::Quadratic {
                    scratch_idx_a,
                    scratch_idx_b,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    I::evaluate_quadratic(
                        &mut eval_scratch,
                        &field_scratch[scratch_idx_a as usize],
                        &field_scratch[scratch_idx_b as usize],
                        &coeff,
                    );
                }
                FoldedEvaluationStep::Linear {
                    scratch_idx,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    I::evaluate_linear(
                        &mut eval_scratch,
                        &field_scratch[scratch_idx as usize],
                        &coeff,
                    );
                }
            }
        }

        if description.total_additive_constant.is_zero() == false {
            I::apply_additive_constant(&mut eval_scratch, &description.total_additive_constant);
        }

        I::apply_eq_suffix(&mut accumulator, &eval_scratch, eq_prefactor);
    }

    accumulator
}
