use super::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::impls::read_ext_and_fold_8;

/// Bridge pass out of a window of 3: three folding challenges are pending, and
/// the next round is evaluated with a plain window of 1 (`[G(0), G_inf]`).
pub struct ExtensionOnlyRoundWindowIn3Out1;

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionOnlyRoundImplementation<F, E>
    for ExtensionOnlyRoundWindowIn3Out1
{
    const INPUT_WINDOW_SIZE: usize = 3;
    const OUTPUT_WINDOW_SIZE: usize = 1;

    type AccumulatorOutput = [E; 2];
    type FoldingPrefix = [E; 8];
    type PerPolyScratch = [E; 2];
    type EvaluationScratch = [E; 2];

    #[inline(always)]
    fn make_accumulation_output() -> Self::AccumulatorOutput {
        [E::ZERO; 2]
    }

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 8
    }

    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 8 / 2
    }

    fn make_prefix_from_all_folding_challenges(
        folding_challenges: &[E],
        worker: &Worker,
    ) -> Self::FoldingPrefix {
        let input_size = <Self as ExtensionOnlyRoundImplementation<F, E>>::INPUT_WINDOW_SIZE;
        assert!(folding_challenges.len() >= input_size);
        make_eq_poly_in_full::<E>(
            &folding_challenges[(folding_challenges.len() - input_size)..],
            worker,
        )
        .pop()
        .unwrap()
        .to_vec()
        .try_into()
        .unwrap()
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
        scratch[0] = E::ZERO;
        scratch[1] = E::ZERO;
    }

    #[inline(always)]
    fn read_then_fold_and_interpolate(
        dst: &mut Self::PerPolyScratch,
        src: &mut DisjointAccessQuasiSlice<E, false>,
        prefix: &Self::FoldingPrefix,
        unfolded_input_size: usize,
        row: usize,
    ) {
        // fold the 3 pending challenges (groups of 8 at stride unfolded/8);
        // the next round variable pairs positions at distance folded/2
        let fold_stride = unfolded_input_size / 8;
        let pair_stride = fold_stride / 2;
        let src_0_idx = row;
        let src_1_idx = src_0_idx + pair_stride;

        let folded_0 = read_ext_and_fold_8(src, prefix, fold_stride, src_0_idx);
        src.write(src_0_idx, folded_0);
        dst[0] = folded_0;

        let folded_1 = read_ext_and_fold_8(src, prefix, fold_stride, src_1_idx);
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
        let fold_stride = unfolded_input_size / 8;
        let pair_stride = fold_stride / 2;
        let src_0_idx = row;
        let src_1_idx = src_0_idx + pair_stride;

        let folded_0 = read_ext_and_fold_8(src, prefix, fold_stride, src_0_idx);
        src.write(src_0_idx, folded_0);
        dst[0] = folded_0;

        let folded_1 = read_ext_and_fold_8(src, prefix, fold_stride, src_1_idx);
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
        // no point at infinity for a linear term
        let mut acc = *coeff;
        acc.mul_assign(&a[0]);
        dst[0].add_assign(&acc);
    }

    #[inline(always)]
    fn apply_additive_constant(dst: &mut Self::EvaluationScratch, coeff: &E) {
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
