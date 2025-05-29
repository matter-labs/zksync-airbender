use crate::butterfly4::Butterfly4;
use crate::radix_4_step::Radix4;
use crate::GoodAllocator;
use field::{Mersenne31Complex, Mersenne31Field};
use trace_holder::RowMajorTrace;
use worker::Worker;

#[inline(always)]
pub fn perform_lde_inplace_vectorized2_recursive_full_trace_parallel<
    const N: usize,
    A: GoodAllocator,
>(
    fft_inverse: &Radix4,
    fft_forward: &Radix4,
    trace: &mut RowMajorTrace<Mersenne31Field, N, A>,
    scales: &[Mersenne31Complex],
    worker: &Worker,
) {
    let trace_len = trace.len();
    assert_eq!(scales.len(), trace_len);

    //IFFT
    let butterfly4 = Butterfly4::new(fft_inverse.direction);
    fft_inverse.cross_fft_recursive_mirrored_full_trace_parallel(
        &mut trace.row_view(0..trace.len()),
        trace_len,
        &butterfly4,
        fft_inverse.twiddles.len(),
        worker,
        1,
    );

    //FFT
    let butterfly4 = Butterfly4::new(fft_forward.direction);
    fft_forward.cross_fft_recursive_scaled_full_trace_parallel(
        &mut trace.row_view(0..trace.len()),
        scales,
        trace_len,
        &butterfly4,
        0,
        worker,
        1,
    );
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bitreverse_enumeration_inplace;
    use crate::grinded_fft::utils::bitreversed_transpose;
    use crate::parallel_row_major_full_line_fft_dit;
    use crate::parallel_row_major_full_line_partial_ifft;
    use crate::FftDirection;
    use crate::LdePrecomputations;
    use crate::Timer;
    use crate::Twiddles;
    use crate::FFT_UNROLL_FACTOR;
    use field::Field;
    use field::Mersenne31Complex;
    use field::Mersenne31Field;
    use field::Rand;
    use std::alloc::Global;
    use trace_holder::RowMajorTrace;
    use worker::Worker;

    pub const TEST_WIDTH: usize = FFT_UNROLL_FACTOR;

    pub fn compute_wide_ldes_ref<const N: usize, A: GoodAllocator>(
        source_domain: RowMajorTrace<Mersenne31Field, N, A>,
        twiddles: &Twiddles<Mersenne31Complex, A>,
        lde_precomputations: &LdePrecomputations<A>,
        source_domain_index: usize,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<RowMajorTrace<Mersenne31Field, N, A>> {
        let mut ldes = Vec::with_capacity(lde_factor);

        let mut source_domain_clone = Some(source_domain.clone());

        let mut partial_ifft = source_domain;
        parallel_row_major_full_line_partial_ifft::<N, A>(
            &mut partial_ifft,
            &twiddles.inverse_twiddles,
            worker,
        );

        let precomputations = lde_precomputations.domain_bound_precomputations[source_domain_index]
            .as_ref()
            .unwrap();

        let now = std::time::Instant::now();
        for (coset_idx, (pows, _tau)) in precomputations
            .bitreversed_powers
            .iter()
            .zip(precomputations.taus.iter())
            .enumerate()
        {
            if coset_idx == source_domain_index {
                let source_domain = source_domain_clone.take().unwrap();
                let coset_values = source_domain;
                ldes.push(coset_values);
            } else {
                // extrapolate
                let mut trace = partial_ifft.clone();
                parallel_row_major_full_line_fft_dit::<N, A>(
                    &mut trace,
                    &twiddles.forward_twiddles_not_bitreversed,
                    pows,
                    worker,
                );

                // parallel_row_major_full_line_fft_dif::<N, A>(
                //     &mut trace,
                //     &twiddles.forward_twiddles,
                //     pows,
                //     worker,
                // );

                let coset_values = trace;

                ldes.push(coset_values);
            }
        }
        dbg!(now.elapsed());

        assert_eq!(ldes.len(), lde_factor);

        ldes
    }

    #[test]
    // #[ignore]
    fn test_grinded_lde_vectorized2_recursive_full_trace_parallel() {
        let trace_len: usize = 1 << 21;
        // let log_n = trace_len.trailing_zeros();
        let num_cores = 8;
        let worker = Worker::new_with_num_threads(num_cores);
        let lde_factor = 2;

        let mut input = vec![Mersenne31Complex::ONE; trace_len];

        let mut rng = rand::rng();
        for i in 0..input.len() {
            input[i] = Mersenne31Complex::random_element(&mut rng);
        }

        //ref
        let num_columns = 256;

        let trace = RowMajorTrace::<Mersenne31Field, TEST_WIDTH, _>::new_zeroed_for_size(
            trace_len,
            num_columns,
            Global,
        );

        let twiddles = Twiddles::<Mersenne31Complex, Global>::new(trace_len, &worker);
        let lde_precomputations =
            LdePrecomputations::<Global>::new(trace_len, lde_factor, &[0, 1], &worker);

        // copy to the trace
        let mut row_view = trace.row_view(0..trace_len);
        for i in 0..trace_len {
            let row = row_view.current_row();
            for pair in row.chunks_mut(2) {
                pair[0] = input[i].c0;
                pair[1] = input[i].c1;
            }
            // row[0] = input[i].c0;
            // row[1] = input[i].c1;
            row_view.advance_row()
        }

        let mut trace_test = trace.clone_parallel(&worker);

        let mut timer = Timer::new();

        // let k = 8; //8; // 16 * 4^k
        // let base_fft = Arc::new(Butterfly16::new(FftDirection::Inverse));
        // let fft_inverse = Radix4::new_with_base(k, base_fft);
        // let base_fft = Arc::new(Butterfly16::new(FftDirection::Forward));
        // let fft_forward = Radix4::new_with_base(k, base_fft);

        let fft_inverse = Radix4::new_with_base(trace_len, FftDirection::Inverse);
        let fft_forward = Radix4::new_with_base(trace_len, FftDirection::Forward);

        //scales
        let mut scales = lde_precomputations.domain_bound_precomputations[0]
            .as_ref()
            .unwrap()
            .bitreversed_powers[1]
            .clone();
        bitreverse_enumeration_inplace(&mut scales);
        let mut scales_transposed = vec![Mersenne31Complex::ZERO; trace_len];
        if trace_len.trailing_zeros() % 2 == 0 {
            bitreversed_transpose::<Mersenne31Complex, 4>(16, &scales, &mut scales_transposed);
        } else {
            bitreversed_transpose::<Mersenne31Complex, 4>(8, &scales, &mut scales_transposed);
        }
        // bitreversed_transpose::<Mersenne31Complex, 4>(16, &scales, &mut scales_transposed);

        timer.measure_running_time("create lde");

        //lde
        // perform_lde_inplace_vectorized2_recursive_full_trace(&fft_inverse, &fft_forward, &mut trace, &scales_transposed);

        let witness_ldes = compute_wide_ldes_ref(
            trace,
            &twiddles,
            &lde_precomputations,
            0,
            lde_factor,
            &worker,
        );

        timer.measure_running_time("perform ref lde");

        //test
        // let mut timer = Timer::new();

        //lde
        perform_lde_inplace_vectorized2_recursive_full_trace_parallel(
            &fft_inverse,
            &fft_forward,
            &mut trace_test,
            &scales_transposed,
            &worker,
        );

        timer.measure_running_time("perform lde");

        //check
        // let mut row_view_ref = trace.row_view(0..trace_len);
        let mut row_view_ref = witness_ldes[1].row_view(0..trace_len);
        let mut row_view_test = trace_test.row_view(0..trace_len);
        for row_idx in 0..trace_len {
            let row_ref = row_view_ref.current_row_ref();
            let row_test = row_view_test.current_row_ref();
            assert_eq!(row_test[0], row_ref[0], "c0 failed at row {}", row_idx);
            assert_eq!(row_test[1], row_ref[1], "c1 failed at row {}", row_idx);
            row_view_ref.advance_row();
            row_view_test.advance_row();
        }
    }
}
