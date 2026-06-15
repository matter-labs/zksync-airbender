use crate::gkr::PAR_THRESHOLD;

use super::*;

pub fn evaluate_initial_with_full_sized_scratch_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    base_field_inputs: Vec<DisjointAccessQuasiSlice<F, false>>,
    ext_field_inputs: Vec<DisjointAccessQuasiSlice<E, false>>,
    description: &BatchEvaluationCompactDescription<F, E>,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 27] {
    assert!(input_size_log2 >= 3);
    let work_size = (1 << input_size_log2) / 8;

    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut acc_chunks = vec![[E::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);

            let base_field_inputs = base_field_inputs.clone();
            let ext_field_inputs = ext_field_inputs.clone();
            let acc_dst = it.next().expect("dst chunk");

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                *acc_dst = evaluate_initial_with_full_sized_scratch(
                    &base_field_inputs,
                    &ext_field_inputs,
                    description,
                    precomputed_eq_suffix,
                    input_size_log2,
                    chunk_start..(chunk_start + chunk_size),
                );
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..27 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

pub fn evaluate_initial_with_full_sized_scratch<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    description: &BatchEvaluationCompactDescription<F, E>,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    row_range: core::ops::Range<usize>,
) -> [E; 27] {
    // NOTE: assuming typical L1 cache size of 32Kb we can fit up to 2k ext field elements for 4th extension, or ~75 ext field fully read
    // and interpolated sets. That is more than sufficient for all our circuits except precompiles, and so we can actually use a strategy to read once
    // and then compute
    assert!(input_size_log2 >= 4);
    assert_eq!(precomputed_eq_suffix.len(), 1 << (input_size_log2 - 3));
    let mut accumulator = [E::ZERO; 27];

    assert_eq!(
        description.base_read_with_interpolation.len(),
        base_field_inputs.len()
    );
    assert_eq!(
        description.ext_read_with_interpolation.len(),
        ext_field_inputs.len()
    );

    let input_size = 1 << input_size_log2;

    let mut base_field_scratch =
        vec![[F::ZERO; 27]; description.base_read_with_interpolation.len()].into_boxed_slice();
    let mut ext_field_scratch =
        vec![[E::ZERO; 27]; description.ext_read_with_interpolation.len()].into_boxed_slice();
    let mut eval_scratch = [E::ZERO; 27];

    for row in row_range {
        let eq_prefactor = &precomputed_eq_suffix[row];
        eval_scratch.fill(E::ZERO);

        // first we read everything

        for ((dst, src), interpolate_at_inf) in base_field_scratch
            .iter_mut()
            .zip(base_field_inputs.iter())
            .zip(description.base_read_with_interpolation.iter())
        {
            if *interpolate_at_inf {
                read_and_interpolate_field(dst, src, input_size, row);
            } else {
                read_without_interpolation(dst, src, input_size, row);
            }
        }

        for ((dst, src), interpolate_at_inf) in ext_field_scratch
            .iter_mut()
            .zip(ext_field_inputs.iter())
            .zip(description.ext_read_with_interpolation.iter())
        {
            if *interpolate_at_inf {
                read_and_interpolate_field(dst, src, input_size, row);
            } else {
                read_without_interpolation(dst, src, input_size, row);
            }
        }

        // and now compute
        for step in description.initial_evaluation_steps.iter() {
            match *step {
                EvaluationStep::QuadraticBaseByBase {
                    scratch_idx_a,
                    scratch_idx_b,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_base(
                        &mut eval_scratch,
                        &base_field_scratch[scratch_idx_a as usize],
                        &base_field_scratch[scratch_idx_b as usize],
                        &coeff,
                    );
                }
                EvaluationStep::QuadraticBaseByExt {
                    scratch_idx_base,
                    scratch_idx_ext,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_mixed(
                        &mut eval_scratch,
                        &ext_field_scratch[scratch_idx_ext as usize],
                        &base_field_scratch[scratch_idx_base as usize],
                        &coeff,
                    );
                }
                EvaluationStep::QuadraticExtByExt {
                    scratch_idx_a,
                    scratch_idx_b,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[scratch_idx_a as usize],
                        &ext_field_scratch[scratch_idx_b as usize],
                        &coeff,
                    );
                }
                EvaluationStep::LinearWithBase {
                    scratch_idx,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_base(
                        &mut eval_scratch,
                        &base_field_scratch[scratch_idx as usize],
                        &coeff,
                    );
                }
                EvaluationStep::LinearWithExt {
                    scratch_idx,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[scratch_idx as usize],
                        &coeff,
                    );
                }
            }
        }

        if description.total_additive_constant.is_zero() == false {
            // only terms that are not at infinity
            for i in 0..2 {
                let offset = 9 * i;
                for j in 0..2 {
                    let offset = offset + 3 * j;
                    for k in 0..2 {
                        eval_scratch[offset + k].add_assign(&description.total_additive_constant);
                    }
                }
            }
        }

        for i in 0..27 {
            let mut t = eval_scratch[i];
            t.mul_assign(eq_prefactor);
            accumulator[i].add_assign(&t);
        }
    }

    accumulator
}
