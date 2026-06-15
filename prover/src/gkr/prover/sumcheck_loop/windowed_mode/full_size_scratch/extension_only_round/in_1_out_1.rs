use super::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::impls::*;

pub struct ExtensionOnlyRoundWindowIn1Out1;

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionOnlyRoundImplementation<F, E>
    for ExtensionOnlyRoundWindowIn1Out1
{
    const INPUT_WINDOW_SIZE: usize = 1;
    const OUTPUT_WINDOW_SIZE: usize = 1;

    type AccumulatorOutput = [E; 2];
    type FoldingPrefix = E;
    type PerPolyScratch = [E; 2];
    type EvaluationScratch = [E; 2];

    #[inline(always)]
    fn make_accumulation_output() -> Self::AccumulatorOutput {
        [E::ZERO; 2]
    }

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 2
    }

    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 2
    }

    fn make_prefix_from_all_folding_challenges(
        folding_challenges: &[E],
        _worker: &Worker,
    ) -> Self::FoldingPrefix {
        let input_size = <Self as ExtensionOnlyRoundImplementation<F, E>>::INPUT_WINDOW_SIZE;
        assert!(folding_challenges.len() >= input_size);
        *folding_challenges.last().expect("challenge")
    }

    #[inline(always)]
    fn reduce_accumulators(mut accs: Vec<Self::AccumulatorOutput>) -> Self::AccumulatorOutput {
        let mut acc = accs.pop().unwrap();
        for el in accs.into_iter() {
            for i in 0..2 {
                acc[i].add_assign(&el[i]);
            }
        }

        acc
    }

    #[inline(always)]
    fn make_poly_scratch() -> Self::PerPolyScratch {
        [E::ZERO; 2]
    }

    #[inline(always)]
    fn make_evaluation_scratch() -> Self::EvaluationScratch {
        [E::ZERO; 2]
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
        let unfolded_input_stride = unfolded_input_size / 2;
        let input_size = unfolded_input_stride;
        let stride_step = input_size / 2;
        let src_0_idx = row;
        let src_1_idx = src_0_idx + stride_step;

        let folded_0 = read_ext_and_fold_2(src, prefix, unfolded_input_stride, src_0_idx);
        src.write(src_0_idx, folded_0);
        dst[0] = folded_0;

        let folded_1 = read_ext_and_fold_2(src, prefix, unfolded_input_stride, src_0_idx);
        src.write(src_1_idx, folded_1);

        dst[1] = interpolate_at_inf_from_0_1_basis(folded_0, folded_1);
    }

    #[inline(always)]
    fn read_then_fold_without_interpolation(
        dst: &mut Self::PerPolyScratch,
        src: &mut DisjointAccessQuasiSlice<E, false>,
        prefix: &Self::FoldingPrefix,
        unfolded_input_size: usize,
        row: usize,
    ) {
        let unfolded_input_stride = unfolded_input_size / 2;
        let input_size = unfolded_input_stride;
        let stride_step = input_size / 2;
        let src_0_idx = row;
        let src_1_idx = src_0_idx + stride_step;

        let folded_0 = read_ext_and_fold_2(src, prefix, unfolded_input_stride, src_0_idx);
        src.write(src_0_idx, folded_0);
        dst[0] = folded_0;

        let folded_1 = read_ext_and_fold_2(src, prefix, unfolded_input_stride, src_0_idx);
        src.write(src_1_idx, folded_1);
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
        // we avoid point of infinity
        let mut acc = *coeff;
        acc.add_assign(&a[0]);
        dst[0].add_assign(&acc);
    }

    #[inline(always)]
    fn apply_additive_constant(dst: &mut Self::EvaluationScratch, coeff: &E) {
        // we avoid point of infinity
        dst[0].add_assign(&coeff);
    }

    #[inline(always)]
    fn apply_eq_suffix(
        dst: &mut Self::AccumulatorOutput,
        src: &Self::EvaluationScratch,
        suffix: &E,
    ) {
        for i in 0..2 {
            let mut t = src[i];
            t.mul_assign(suffix);
            dst[i].add_assign(&t);
        }
    }
}
