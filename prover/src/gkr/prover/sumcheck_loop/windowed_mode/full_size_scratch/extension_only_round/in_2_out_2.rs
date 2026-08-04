use super::*;

pub struct ExtensionOnlyRoundWindowIn2Out2;

#[inline(always)]
fn read_ext_and_fold_4<F: Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    precomputed_eq_prefix: &[F; 4],
    stride: usize,
    row: usize,
) -> F {
    let mut offset = row;
    let mut result = precomputed_eq_prefix[0];
    result.mul_assign(&src.read(offset));
    offset += stride;
    for i in 1..4 {
        let mut t = precomputed_eq_prefix[i];
        t.mul_assign(&src.read(offset));
        result.add_assign(&t);
        offset += stride;
    }

    result
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionOnlyRoundImplementation<F, E>
    for ExtensionOnlyRoundWindowIn2Out2
{
    const INPUT_WINDOW_SIZE: usize = 2;
    const OUTPUT_WINDOW_SIZE: usize = 2;

    type AccumulatorOutput = [E; 9];
    type FoldingPrefix = [E; 4];
    type PerPolyScratch = [E; 9];
    type EvaluationScratch = [E; 9];

    #[inline(always)]
    fn make_accumulation_output() -> Self::AccumulatorOutput {
        [E::ZERO; 9]
    }

    fn folded_buffer_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 4
    }

    fn work_size_for_unfolded_input_size(input_size_log2: usize) -> usize {
        (1 << input_size_log2) / 4 / 4
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
            for i in 0..9 {
                acc[i].add_assign(&el[i]);
            }
        }

        acc
    }

    #[inline(always)]
    fn make_poly_scratch() -> Self::PerPolyScratch {
        [E::ZERO; 9]
    }

    #[inline(always)]
    fn make_evaluation_scratch() -> Self::EvaluationScratch {
        [E::ZERO; 9]
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
        // fold groups of 4 (the two pending challenges), then fill the 9-cell
        // {0, 1, inf}^2 grid over the next two window variables
        let unfolded_input_stride = unfolded_input_size / 4;
        let a_stride = unfolded_input_stride / 2;
        let b_stride = unfolded_input_stride / 4;

        for a in 0..2 {
            for b in 0..2 {
                let idx = row + a * a_stride + b * b_stride;
                let folded = read_ext_and_fold_4(src, prefix, unfolded_input_stride, idx);
                src.write(idx, folded);
                dst[3 * a + b] = folded;
            }
            dst[3 * a + 2] = interpolate_at_inf_from_0_1_basis(dst[3 * a], dst[3 * a + 1]);
        }

        for k in 0..3 {
            dst[6 + k] = interpolate_at_inf_from_0_1_basis(dst[k], dst[3 + k]);
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
        let unfolded_input_stride = unfolded_input_size / 4;
        let a_stride = unfolded_input_stride / 2;
        let b_stride = unfolded_input_stride / 4;

        for a in 0..2 {
            for b in 0..2 {
                let idx = row + a * a_stride + b * b_stride;
                let folded = read_ext_and_fold_4(src, prefix, unfolded_input_stride, idx);
                src.write(idx, folded);
                dst[3 * a + b] = folded;
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
        // only cells with no coordinate at infinity
        for i in 0..2 {
            for j in 0..2 {
                let offset = 3 * i + j;
                let mut acc = *coeff;
                acc.mul_assign(&a[offset]);
                dst[offset].add_assign(&acc);
            }
        }
    }

    #[inline(always)]
    fn apply_additive_constant(dst: &mut Self::EvaluationScratch, coeff: &E) {
        // only cells with no coordinate at infinity
        for i in 0..2 {
            for j in 0..2 {
                dst[3 * i + j].add_assign(&coeff);
            }
        }
    }

    #[inline(always)]
    fn apply_eq_suffix(
        dst: &mut Self::AccumulatorOutput,
        src: &Self::EvaluationScratch,
        suffix: &E,
    ) {
        for i in 0..9 {
            let mut t = src[i];
            t.mul_assign(suffix);
            dst[i].add_assign(&t);
        }
    }
}
