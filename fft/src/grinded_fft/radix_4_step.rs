use super::*;
use crate::butterfly8::Butterfly8;
use butterfly16::Butterfly16;
use butterfly4::Butterfly4;
use butterfly4::{
    butterfly_4_vectorized2_full_trace, butterfly_4_vectorized2_full_trace_parallel,
    butterfly_4_vectorized2_mirrored_full_trace,
    butterfly_4_vectorized2_mirrored_full_trace_parallel,
};
use field::FieldLikeVectorized;
use field::Mersenne31ComplexVectorized;
use field::{Mersenne31Complex, Mersenne31Field};
use std::sync::Arc;
use trace_holder::RowMajorTraceView;
use worker::Worker;

pub struct Radix4 {
    pub twiddles: Box<[Mersenne31Complex]>,

    base_fft_even: Arc<Butterfly16>,
    base_fft_odd: Arc<Butterfly8>,
    base_len: usize,

    len: usize,
    pub direction: FftDirection,
    inplace_scratch_len: usize,
    outofplace_scratch_len: usize,
}

impl Radix4 {
    /// Constructs a Radix4 instance which computes FFTs of length `4^k * base_fft.len()`
    pub fn new_with_base(domain_size: usize, direction: FftDirection) -> Self {
        let base_fft_even = Arc::new(Butterfly16::new(direction));
        let base_fft_odd = Arc::new(Butterfly8::new(direction));

        let (k, base_len) = {
            let k = (domain_size >> 4).trailing_zeros() >> 1;

            if domain_size.trailing_zeros() % 2 == 0 {
                (k, base_fft_even.len())
            } else {
                (k + 1, base_fft_odd.len())
            }
        };

        let len = base_len * (1 << (k * 2));

        // precompute the twiddle factors this algorithm will use.
        // we're doing the same precomputation of twiddle factors as the mixed radix algorithm where width=4 and height=len/4
        // but mixed radix only does one step and then calls itself recursively, and this algorithm does every layer all the way down
        // so we're going to pack all the "layers" of twiddle factors into a single array, starting with the bottom layer and going up
        const ROW_COUNT: usize = 4;
        let mut cross_fft_len = base_len;
        let mut twiddle_factors = Vec::with_capacity(len * 2);
        while cross_fft_len < len {
            let num_columns = cross_fft_len;
            cross_fft_len *= ROW_COUNT;

            for i in 0..num_columns {
                for k in 1..ROW_COUNT {
                    let twiddle = twiddles::compute_twiddle(i * k, cross_fft_len, direction);
                    twiddle_factors.push(twiddle);
                }
            }
        }
        // println!("cross_fft_len: {:?}", cross_fft_len);

        let inplace_scratch_len = cross_fft_len;
        let outofplace_scratch_len = 0;

        Self {
            twiddles: twiddle_factors.into_boxed_slice(),

            base_fft_even,
            base_fft_odd,
            base_len,

            len,
            direction,

            inplace_scratch_len,
            outofplace_scratch_len,
        }
    }

    pub fn inplace_scratch_len(&self) -> usize {
        self.inplace_scratch_len
    }
    pub fn outofplace_scratch_len(&self) -> usize {
        self.outofplace_scratch_len
    }

    #[inline(always)]
    pub fn cross_fft_recursive_mirrored_full_trace<const N: usize>(
        &self,
        trace: &RowMajorTraceView<Mersenne31Field, N>,
        cross_fft_len: usize,
        butterfly4: &Butterfly4,
        twiddle_offset: usize,
    ) {
        let num_columns = cross_fft_len / 4;
        let twiddle_offset = twiddle_offset - num_columns * 3;
        let layer_twiddles = &self.twiddles[twiddle_offset..];
        unsafe {
            butterfly_4_vectorized2_mirrored_full_trace(
                &mut trace.row_view(0..trace.len()),
                &layer_twiddles[..],
                num_columns,
                &butterfly4,
            );
        }

        let cross_fft_len = cross_fft_len / 4;
        let num_columns = cross_fft_len / 4;

        if cross_fft_len == self.base_len * 4 {
            let layer_twiddles = &self.twiddles[..];

            for i in 0..4 {
                let mut chunk = trace.row_view(i * cross_fft_len..(i + 1) * cross_fft_len);
                unsafe {
                    butterfly_4_vectorized2_mirrored_full_trace(
                        &mut chunk,
                        layer_twiddles,
                        num_columns,
                        &butterfly4,
                    );
                }

                for j in 0..4 {
                    let mut chunk_base = chunk.row_view(j * self.base_len..(j + 1) * self.base_len);

                    unsafe {
                        if self.base_len == 16 {
                            self.base_fft_even
                                .perform_fft_contiguous_vectorized2_full_trace(&mut chunk_base);
                        } else if self.base_len == 8 {
                            self.base_fft_odd
                                .perform_fft_contiguous_vectorized2_full_trace(&mut chunk_base);
                        } else {
                            panic!("Unsupported base_len");
                        }
                    }
                }
            }
        } else {
            self.cross_fft_recursive_mirrored_full_trace(
                &trace.row_view(3 * cross_fft_len..4 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            self.cross_fft_recursive_mirrored_full_trace(
                &trace.row_view(2 * cross_fft_len..3 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            self.cross_fft_recursive_mirrored_full_trace(
                &trace.row_view(cross_fft_len..2 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            self.cross_fft_recursive_mirrored_full_trace(
                &trace.row_view(0..cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
        };
    }

    #[inline(always)]
    pub fn cross_fft_recursive_scaled_full_trace<const N: usize>(
        &self,
        trace: &RowMajorTraceView<Mersenne31Field, N>,
        scales: &[Mersenne31Complex],
        cross_fft_len: usize,
        butterfly4: &Butterfly4,
        twiddle_offset: usize,
    ) -> usize {
        let cross_fft_len = cross_fft_len / 4;
        let num_columns = cross_fft_len / 4;

        let new_twiddle_offset = if cross_fft_len == self.base_len * 4 {
            let layer_twiddles = &self.twiddles[twiddle_offset..];

            for i in 0..4 {
                let mut chunk = trace.row_view(i * cross_fft_len..(i + 1) * cross_fft_len);
                let scales_chunk = &scales[i * cross_fft_len..(i + 1) * cross_fft_len];

                for j in 0..4 {
                    let mut chunk_base = chunk.row_view(j * self.base_len..(j + 1) * self.base_len);
                    let scales_chunk_base =
                        &scales_chunk[j * self.base_len..(j + 1) * self.base_len];
                    unsafe {
                        for (idx, scale) in scales_chunk_base.iter().enumerate() {
                            let scale_vec = Mersenne31ComplexVectorized::constant(*scale);
                            chunk_base
                                .get_row_mut_vectorized(idx)
                                .iter_mut()
                                .for_each(|x| *x = *x * scale_vec);
                        }

                        if self.base_len == 16 {
                            self.base_fft_even
                                .perform_fft_contiguous_vectorized2_full_trace(&mut chunk_base);
                        } else if self.base_len == 8 {
                            self.base_fft_odd
                                .perform_fft_contiguous_vectorized2_full_trace(&mut chunk_base);
                        } else {
                            panic!("Unsupported base_len");
                        }
                    }
                }

                unsafe {
                    butterfly_4_vectorized2_full_trace(
                        &mut chunk,
                        layer_twiddles,
                        num_columns,
                        &butterfly4,
                    );
                }
            }

            0
        } else {
            self.cross_fft_recursive_scaled_full_trace(
                &trace.row_view(0..cross_fft_len),
                &scales[..cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            self.cross_fft_recursive_scaled_full_trace(
                &trace.row_view(cross_fft_len..2 * cross_fft_len),
                &scales[cross_fft_len..2 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            self.cross_fft_recursive_scaled_full_trace(
                &trace.row_view(2 * cross_fft_len..3 * cross_fft_len),
                &scales[2 * cross_fft_len..3 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );
            let new_twiddle_offset = self.cross_fft_recursive_scaled_full_trace(
                &trace.row_view(3 * cross_fft_len..4 * cross_fft_len),
                &scales[3 * cross_fft_len..4 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
            );

            new_twiddle_offset
        };

        let twiddle_offset = num_columns * 3 + new_twiddle_offset;
        // println!("twiddle_offset ref: {:?}", twiddle_offset);
        let layer_twiddles = &self.twiddles[twiddle_offset..];

        unsafe {
            butterfly_4_vectorized2_full_trace(
                &mut trace.row_view(0..trace.len()),
                layer_twiddles,
                num_columns * 4,
                &butterfly4,
            );
        }

        twiddle_offset
    }

    #[inline(always)]
    pub fn cross_fft_recursive_mirrored_full_trace_parallel<const N: usize>(
        &self,
        trace: &RowMajorTraceView<Mersenne31Field, N>,
        cross_fft_len: usize,
        butterfly4: &Butterfly4,
        twiddle_offset: usize,
        worker: &Worker,
        depth: usize,
    ) {
        let new_depth = depth * 4;
        if depth >= worker.get_num_cores() {
            // fallthrough
        } else {
            let num_columns = cross_fft_len / 4;
            let twiddle_offset = twiddle_offset - num_columns * 3;
            let layer_twiddles = &self.twiddles[twiddle_offset..];
            unsafe {
                butterfly_4_vectorized2_mirrored_full_trace_parallel(
                    &mut trace.row_view(0..trace.len()),
                    &layer_twiddles[..],
                    num_columns,
                    &butterfly4,
                    &worker,
                );
            }

            let cross_fft_len = cross_fft_len / 4;
            // let num_columns = cross_fft_len / 4;

            self.cross_fft_recursive_mirrored_full_trace_parallel(
                &trace.row_view(3 * cross_fft_len..4 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            self.cross_fft_recursive_mirrored_full_trace_parallel(
                &trace.row_view(2 * cross_fft_len..3 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            self.cross_fft_recursive_mirrored_full_trace_parallel(
                &trace.row_view(cross_fft_len..2 * cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            self.cross_fft_recursive_mirrored_full_trace_parallel(
                &trace.row_view(0..cross_fft_len),
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
        }

        // flatten the recursion
        if depth == 1 {
            let work_size_log = (worker.get_num_cores() as f64).log(4.0).ceil() as usize;
            let work_size = 1 << (work_size_log * 2);
            let mut cross_fft_len = cross_fft_len;
            let mut twiddle_offset = twiddle_offset;
            for _ in 0..work_size_log {
                let num_columns = cross_fft_len / 4;
                twiddle_offset -= num_columns * 3;
                cross_fft_len /= 4;
            }
            // println!("work_size: {:?}", work_size);
            worker.scope(work_size, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    // println!("thread_idx: {:?}, chunk_start: {:?}, chunk_size: {:?}", thread_idx, chunk_start, chunk_size);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for idx in chunk_start..chunk_start + chunk_size {
                            // println!("range: {:?}", idx * cross_fft_len..(idx + 1) * cross_fft_len);
                            self.cross_fft_recursive_mirrored_full_trace(
                                &trace.row_view(idx * cross_fft_len..(idx + 1) * cross_fft_len),
                                cross_fft_len,
                                butterfly4,
                                twiddle_offset,
                            );
                        }
                    });
                }
            });
        }
    }

    #[inline(always)]
    pub fn cross_fft_recursive_scaled_full_trace_parallel<const N: usize>(
        &self,
        trace: &RowMajorTraceView<Mersenne31Field, N>,
        scales: &[Mersenne31Complex],
        cross_fft_len: usize,
        butterfly4: &Butterfly4,
        twiddle_offset: usize,
        worker: &Worker,
        depth: usize,
    ) -> usize {
        //flatten the recursion
        if depth == 1 {
            // println!("flatten the recursion");
            let work_size_log = (worker.get_num_cores() as f64).log(4.0).ceil() as usize;
            let work_size = 1 << (work_size_log * 2);
            let cross_fft_len = cross_fft_len / work_size;
            // println!("work_size: {:?}", work_size);
            worker.scope(work_size, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    // println!("thread_idx: {:?}, chunk_start: {:?}, chunk_size: {:?}", thread_idx, chunk_start, chunk_size);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for idx in chunk_start..chunk_start + chunk_size {
                            // println!("range: {:?}", idx * cross_fft_len..(idx + 1) * cross_fft_len);
                            self.cross_fft_recursive_scaled_full_trace(
                                &trace.row_view(idx * cross_fft_len..(idx + 1) * cross_fft_len),
                                &scales[idx * cross_fft_len..(idx + 1) * cross_fft_len],
                                cross_fft_len,
                                butterfly4,
                                0,
                            );
                        }
                    });
                }
            });
        }

        // println!("cross_fft depth: {:?}", depth);
        let new_depth = depth * 4;
        let new_twiddle_offset = if depth >= worker.get_num_cores() {
            // println!("return, new_depth: {:?}", new_depth);
            let work_size_log = (worker.get_num_cores() as f64).log(4.0).ceil() as usize;
            let mut cross_fft_len = self.len();
            let mut twiddle_offset = self.twiddles.len();
            // println!("self.twiddles.len(): {:?}", self.twiddles.len());
            for _ in 0..work_size_log + 1 {
                let num_columns = cross_fft_len / 4;
                twiddle_offset -= num_columns * 3;
                // println!("twiddle_offset intermediate: {:?}", twiddle_offset);
                cross_fft_len /= 4;
            }
            // println!("twiddle_offset on return: {:?}", twiddle_offset);
            twiddle_offset
        } else {
            let cross_fft_len = cross_fft_len / 4;
            let num_columns = cross_fft_len / 4;

            self.cross_fft_recursive_scaled_full_trace_parallel(
                &mut trace.row_view(0..cross_fft_len),
                &scales[..cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            self.cross_fft_recursive_scaled_full_trace_parallel(
                &mut trace.row_view(cross_fft_len..2 * cross_fft_len),
                &scales[cross_fft_len..2 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            self.cross_fft_recursive_scaled_full_trace_parallel(
                &mut trace.row_view(2 * cross_fft_len..3 * cross_fft_len),
                &scales[2 * cross_fft_len..3 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );
            let new_twiddle_offset = self.cross_fft_recursive_scaled_full_trace_parallel(
                &mut trace.row_view(3 * cross_fft_len..4 * cross_fft_len),
                &scales[3 * cross_fft_len..4 * cross_fft_len],
                cross_fft_len,
                butterfly4,
                twiddle_offset,
                worker,
                new_depth,
            );

            let twiddle_offset = num_columns * 3 + new_twiddle_offset;
            // println!("twiddle_offset: {:?}", twiddle_offset);
            let layer_twiddles = &self.twiddles[twiddle_offset..];

            unsafe {
                butterfly_4_vectorized2_full_trace_parallel(
                    &mut trace.row_view(0..trace.len()),
                    layer_twiddles,
                    num_columns * 4,
                    &butterfly4,
                    worker,
                );
            }

            twiddle_offset
        };

        new_twiddle_offset
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }
    #[inline(always)]
    pub fn fft_direction(&self) -> FftDirection {
        self.direction
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bitreverse_enumeration_inplace;
    use crate::grinded_fft::utils::bitreversed_transpose_mirrored;
    use crate::precompute_all_twiddles_for_fft_serial;
    use crate::serial_ct_ntt_natural_to_bitreversed;
    use crate::FftDirection;
    use crate::Timer;
    use crate::FFT_UNROLL_FACTOR;
    use field::Field;
    use field::Mersenne31Complex;
    use field::Mersenne31Field;
    use field::Rand;
    use std::alloc::Global;
    use trace_holder::RowMajorTrace;

    pub const TEST_WIDTH: usize = FFT_UNROLL_FACTOR;

    #[test]
    // #[ignore]
    fn test_ifft_nontransposed() {
        let trace_len: usize = 1 << 9;
        let log_n = trace_len.trailing_zeros();

        let mut input = vec![Mersenne31Complex::ONE; trace_len];

        let mut rng = rand::rng();
        for i in 0..input.len() {
            input[i] = Mersenne31Complex::random_element(&mut rng);
        }

        //ref
        let num_columns = 32;

        let trace = RowMajorTrace::<Mersenne31Field, TEST_WIDTH, _>::new_zeroed_for_size(
            trace_len,
            num_columns,
            Global,
        );

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

        let mut timer = Timer::new();

        let fft_inverse = Radix4::new_with_base(trace_len, FftDirection::Inverse);

        timer.measure_running_time("create lde");

        //lde

        let omegas_bit_reversed: Vec<Mersenne31Complex, Global> =
            precompute_all_twiddles_for_fft_serial::<Mersenne31Complex, Global, true>(trace_len);

        let mut input_ref = input.clone();
        serial_ct_ntt_natural_to_bitreversed(&mut input_ref, log_n, &omegas_bit_reversed);
        bitreverse_enumeration_inplace(&mut input_ref);

        timer.measure_running_time("perform ref lde");

        //test

        let butterfly4 = Butterfly4::new(fft_inverse.direction);
        fft_inverse.cross_fft_recursive_mirrored_full_trace(
            &mut trace.row_view(0..trace.len()),
            trace_len,
            &butterfly4,
            fft_inverse.twiddles.len(),
        );

        timer.measure_running_time("perform lde");

        let mut result = vec![Mersenne31Complex::ZERO; trace_len];
        let mut row_view_test = trace.row_view(0..trace_len);
        for row_idx in 0..trace_len {
            let row = row_view_test.current_row_ref();
            result[row_idx] = Mersenne31Complex {
                c0: row[0],
                c1: row[1],
            };
            row_view_test.advance_row();
        }

        let mut result_transposed = vec![Mersenne31Complex::ZERO; trace_len];
        bitreversed_transpose_mirrored::<_, 4>(
            8,
            &result[0..trace_len],
            &mut result_transposed[0..trace_len],
        );

        //check
        for row_idx in 0..trace_len {
            assert_eq!(
                input_ref[row_idx], result_transposed[row_idx],
                "failed at row {}",
                row_idx
            );
        }
    }
}
