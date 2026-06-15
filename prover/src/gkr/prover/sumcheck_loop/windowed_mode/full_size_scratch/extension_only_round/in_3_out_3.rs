use super::*;

pub struct ExtensionOnlyRoundWindowIn3Out3;

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionOnlyRoundImplementation<F, E>
    for ExtensionOnlyRoundWindowIn3Out3
{
    const INPUT_WINDOW_SIZE: usize = 3;
    const OUTPUT_WINDOW_SIZE: usize = 3;

    type AccumulatorOutput = [E; 27];
    type FoldingPrefix = [E; 8];
    type PerPolyScratch = [E; 27];
    type EvaluationScratch = [E; 27];

    #[inline(always)]
    fn make_accumulation_output() -> Self::AccumulatorOutput {
        [E::ZERO; 27]
    }

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 8
    }

    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 8 / 8
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
        input_size: usize,
        row: usize,
    ) {
        read_ext_then_fold_and_interpolate_inplace(dst, src, input_size, prefix, row);
    }

    #[inline(always)]
    fn read_then_fold_without_interpolation(
        dst: &mut Self::PerPolyScratch,
        src: &mut DisjointAccessQuasiSlice<E, false>,
        prefix: &Self::FoldingPrefix,
        input_size: usize,
        row: usize,
    ) {
        read_ext_then_fold_without_interpolation_inplace(dst, src, input_size, prefix, row);
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
        for i in 0..27 {
            let mut t = src[i];
            t.mul_assign(suffix);
            dst[i].add_assign(&t);
        }
    }
}
