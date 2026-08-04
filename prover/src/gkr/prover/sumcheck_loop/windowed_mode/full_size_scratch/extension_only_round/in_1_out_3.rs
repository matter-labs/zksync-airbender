use super::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::impls::read_ext_and_fold_2;

/// Bridge pass used right after the `in 3, out 1` transition round: only ONE
/// folding challenge is pending, and we open a new window of 3 variables.
pub struct ExtensionOnlyRoundWindowIn1Out3;

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionOnlyRoundImplementation<F, E>
    for ExtensionOnlyRoundWindowIn1Out3
{
    const INPUT_WINDOW_SIZE: usize = 1;
    const OUTPUT_WINDOW_SIZE: usize = 3;

    type AccumulatorOutput = [E; 27];
    type FoldingPrefix = E;
    type PerPolyScratch = [E; 27];
    type EvaluationScratch = [E; 27];

    #[inline(always)]
    fn make_accumulation_output() -> Self::AccumulatorOutput {
        [E::ZERO; 27]
    }

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 2
    }

    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 2 / 8
    }

    fn make_prefix_from_all_folding_challenges(
        folding_challenges: &[E],
        _worker: &Worker,
    ) -> Self::FoldingPrefix {
        assert!(folding_challenges.len() >= 1);
        *folding_challenges.last().expect("challenge")
    }

    #[inline(always)]
    fn reduce_accumulators(mut accs: Vec<Self::AccumulatorOutput>) -> Self::AccumulatorOutput {
        let mut acc = accs.pop().unwrap();
        for el in accs.into_iter() {
            for i in 0..27 {
                acc[i].add_assign(&el[i]);
            }
        }

        acc
    }

    #[inline(always)]
    fn make_poly_scratch() -> Self::PerPolyScratch {
        [E::ZERO; 27]
    }

    #[inline(always)]
    fn make_evaluation_scratch() -> Self::EvaluationScratch {
        [E::ZERO; 27]
    }

    #[inline(always)]
    fn clear_evaluation_scratch(scratch: &mut Self::EvaluationScratch) {
        scratch.fill(E::ZERO);
    }

    #[inline(always)]
    fn read_then_fold_and_interpolate(
        dst: &mut Self::PerPolyScratch,
        src: &mut DisjointAccessQuasiSlice<E, false>,
        prefix: &Self::FoldingPrefix,
        unfolded_input_size: usize,
        row: usize,
    ) {
        // fold the single pending challenge (pairs at distance unfolded/2),
        // then fill the {0,1,inf}^3 grid over the next three window variables
        let fold_stride = unfolded_input_size / 2;
        let input_size = fold_stride;
        let stride_step = input_size / 2;
        for x0 in 0..2 {
            let stride = stride_step * x0;
            let dst_offset = 9 * x0;
            for x1 in 0..2 {
                let stride_step = stride_step / 2;
                let stride = stride + x1 * stride_step;
                let dst_offset = dst_offset + 3 * x1;
                {
                    let stride_step = stride_step / 2;
                    let src_0_idx = stride + row;
                    let src_1_idx = src_0_idx + stride_step;

                    let folded_0 = read_ext_and_fold_2(src, prefix, fold_stride, src_0_idx);
                    src.write(src_0_idx, folded_0);
                    dst[dst_offset] = folded_0;

                    let folded_1 = read_ext_and_fold_2(src, prefix, fold_stride, src_1_idx);
                    src.write(src_1_idx, folded_1);
                    dst[dst_offset + 1] = folded_1;

                    dst[dst_offset + 2] =
                        interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
                }
            }

            // inf over x1
            for x2 in 0..3 {
                let src_0_idx = dst_offset + x2;
                let src_1_idx = dst_offset + 3 + x2;
                dst[dst_offset + 3 * 2 + x2] =
                    interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
            }
        }

        // inf over x0
        for x1 in 0..3 {
            let dst_offset = 3 * x1;
            for x2 in 0..3 {
                let src_0_idx = 0 + dst_offset + x2;
                let src_1_idx = 9 + dst_offset + x2;
                dst[18 + dst_offset + x2] =
                    interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
            }
        }
    }

    #[inline(always)]
    fn read_then_fold_without_interpolation(
        dst: &mut Self::PerPolyScratch,
        src: &mut DisjointAccessQuasiSlice<E, false>,
        prefix: &Self::FoldingPrefix,
        unfolded_input_size: usize,
        row: usize,
    ) {
        let fold_stride = unfolded_input_size / 2;
        let input_size = fold_stride;
        let stride_step = input_size / 2;
        for x0 in 0..2 {
            let stride = stride_step * x0;
            let dst_offset = 9 * x0;
            for x1 in 0..2 {
                let stride_step = stride_step / 2;
                let stride = stride + x1 * stride_step;
                let dst_offset = dst_offset + 3 * x1;
                {
                    let stride_step = stride_step / 2;
                    let src_0_idx = stride + row;
                    let src_1_idx = src_0_idx + stride_step;

                    let folded_0 = read_ext_and_fold_2(src, prefix, fold_stride, src_0_idx);
                    src.write(src_0_idx, folded_0);
                    dst[dst_offset] = folded_0;

                    let folded_1 = read_ext_and_fold_2(src, prefix, fold_stride, src_1_idx);
                    src.write(src_1_idx, folded_1);
                    dst[dst_offset + 1] = folded_1;
                }
            }
        }
    }

    #[inline(always)]
    fn evaluate_quadratic(
        dst: &mut Self::EvaluationScratch,
        a: &Self::PerPolyScratch,
        b: &Self::PerPolyScratch,
        coeff: &E,
    ) {
        evaluate_quadratic_ext(dst, a, b, coeff);
    }

    #[inline(always)]
    fn evaluate_linear(dst: &mut Self::EvaluationScratch, a: &Self::PerPolyScratch, coeff: &E) {
        evaluate_linear_ext(dst, a, coeff);
    }

    #[inline(always)]
    fn apply_additive_constant(dst: &mut Self::EvaluationScratch, coeff: &E) {
        // only terms that are not at infinity
        for i in 0..2 {
            let offset = 9 * i;
            for j in 0..2 {
                let offset = offset + 3 * j;
                for k in 0..2 {
                    dst[offset + k].add_assign(&coeff);
                }
            }
        }
    }

    #[inline(always)]
    fn apply_eq_suffix(
        dst: &mut Self::AccumulatorOutput,
        src: &Self::EvaluationScratch,
        suffix: &E,
    ) {
        accumulate_scaled(dst, src, suffix);
    }
}
