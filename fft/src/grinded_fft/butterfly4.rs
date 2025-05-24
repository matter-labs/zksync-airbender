use super::*;
use crate::grinded_fft::utils::Load;
use crate::grinded_fft::utils::LoadStore;
use butterfly2::Butterfly2;
use field::FieldLikeVectorized;
use field::Mersenne31ComplexVectorized;
use field::Mersenne31ComplexVectorizedInterleaved;
use field::{Mersenne31Complex, Mersenne31Field};
use trace_holder::RowMajorTraceView;
use worker::Worker;

#[derive(Clone, Copy, Debug)]
pub struct Butterfly4 {
    direction: FftDirection,
}
impl Butterfly4 {
    #[inline(always)]
    pub fn new(direction: FftDirection) -> Self {
        Self { direction }
    }
    #[inline(always)]
    pub unsafe fn perform_fft_contiguous(&self, mut buffer: impl LoadStore<Mersenne31Complex>) {
        //we're going to hardcode a step of mixed radix
        //aka we're going to do the six step algorithm

        // step 1: transpose, which we're skipping because we're just going to perform non-contiguous FFTs
        let mut value0 = buffer.load(0);
        let mut value1 = buffer.load(1);
        let mut value2 = buffer.load(2);
        let mut value3 = buffer.load(3);

        // step 2: column FFTs
        Butterfly2::perform_fft_strided(&mut value0, &mut value2);
        Butterfly2::perform_fft_strided(&mut value1, &mut value3);

        // step 3: apply twiddle factors (only one in this case, and it's either 0 + i or 0 - i)
        value3 = twiddles::rotate_90(value3, self.direction);

        // step 4: transpose, which we're skipping because we're the previous FFTs were non-contiguous

        // step 5: row FFTs
        Butterfly2::perform_fft_strided(&mut value0, &mut value1);
        Butterfly2::perform_fft_strided(&mut value2, &mut value3);

        // step 6: transpose by swapping index 1 and 2
        buffer.store(value0, 0);
        buffer.store(value2, 1);
        buffer.store(value1, 2);
        buffer.store(value3, 3);
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn perform_fft_contiguous_vectorized2_full_trace(
        &self,
        row0: &mut [Mersenne31ComplexVectorizedInterleaved],
        row1: &mut [Mersenne31ComplexVectorizedInterleaved],
        row2: &mut [Mersenne31ComplexVectorizedInterleaved],
        row3: &mut [Mersenne31ComplexVectorizedInterleaved],
    ) {
        //we're going to hardcode a step of mixed radix
        //aka we're going to do the six step algorithm

        // step 1: transpose, which we're skipping because we're just going to perform non-contiguous FFTs

        // step 2: column FFTs
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row0, row2);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row1, row3);

        // step 3: apply twiddle factors (only one in this case, and it's either 0 + i or 0 - i)
        for v3 in row3.iter_mut() {
            *v3 = twiddles::rotate_90_vectorized2(*v3, self.direction);
        }

        // step 4: transpose, which we're skipping because we're the previous FFTs were non-contiguous

        // step 5: row FFTs
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row0, row1);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row2, row3);

        // step 6: transpose by swapping index 1 and 2
        for i in 0..row1.len() {
            let temp = row1[i];
            row1[i] = row2[i];
            row2[i] = temp;
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        4
    }
    #[inline(always)]
    pub fn fft_direction(&self) -> FftDirection {
        self.direction
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub(crate) unsafe fn butterfly_4_vectorized2_full_trace<const N: usize>(
    trace: &mut RowMajorTraceView<Mersenne31Field, N>,
    twiddles: impl Load,
    num_columns: usize,
    butterfly4: &Butterfly4,
) {
    // println!("num_columns: {}", num_columns);
    for idx in 0..num_columns {
        let tw_idx = idx * 3;

        let mut row0 = trace.get_row_mut_vectorized(idx + 0 * num_columns);
        let mut row1 = trace.get_row_mut_vectorized(idx + 1 * num_columns);
        let mut row2 = trace.get_row_mut_vectorized(idx + 2 * num_columns);
        let mut row3 = trace.get_row_mut_vectorized(idx + 3 * num_columns);

        let twiddle0 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 0));
        let twiddle1 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 1));
        let twiddle2 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 2));

        for i in 0..row1.len() {
            row1[i] = row1[i] * twiddle0;
            row2[i] = row2[i] * twiddle1;
            row3[i] = row3[i] * twiddle2;
        }

        butterfly4.perform_fft_contiguous_vectorized2_full_trace(
            &mut row0, &mut row1, &mut row2, &mut row3,
        );
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub(crate) unsafe fn butterfly_4_vectorized2_mirrored_full_trace<const N: usize>(
    trace: &mut RowMajorTraceView<Mersenne31Field, N>,
    twiddles: impl Load,
    num_columns: usize,
    butterfly4: &Butterfly4,
) {
    // println!("num_columns: {}", num_columns);
    for idx in 0..num_columns {
        let tw_idx = idx * 3;

        let mut row0 = trace.get_row_mut_vectorized(idx + 0 * num_columns);
        let mut row1 = trace.get_row_mut_vectorized(idx + 1 * num_columns);
        let mut row2 = trace.get_row_mut_vectorized(idx + 2 * num_columns);
        let mut row3 = trace.get_row_mut_vectorized(idx + 3 * num_columns);

        butterfly4.perform_fft_contiguous_vectorized2_full_trace(
            &mut row0, &mut row1, &mut row2, &mut row3,
        );

        let twiddle0 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 0));
        let twiddle1 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 1));
        let twiddle2 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 2));

        for i in 0..row1.len() {
            row1[i] = row1[i] * twiddle0;
            row2[i] = row2[i] * twiddle1;
            row3[i] = row3[i] * twiddle2;
        }
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub(crate) unsafe fn butterfly_4_vectorized2_full_trace_parallel<const N: usize>(
    trace: &RowMajorTraceView<Mersenne31Field, N>,
    twiddles: impl Load,
    num_columns: usize,
    butterfly4: &Butterfly4,
    worker: &Worker,
) {
    // println!("num_columns: {}", num_columns);
    worker.scope(num_columns, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for idx in chunk_start..chunk_start + chunk_size {
                    let tw_idx = idx * 3;

                    let mut row0 = trace.get_row_mut_vectorized(idx + 0 * num_columns);
                    let mut row1 = trace.get_row_mut_vectorized(idx + 1 * num_columns);
                    let mut row2 = trace.get_row_mut_vectorized(idx + 2 * num_columns);
                    let mut row3 = trace.get_row_mut_vectorized(idx + 3 * num_columns);

                    let twiddle0 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 0));
                    let twiddle1 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 1));
                    let twiddle2 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 2));

                    for i in 0..row1.len() {
                        row1[i] = row1[i] * twiddle0;
                        row2[i] = row2[i] * twiddle1;
                        row3[i] = row3[i] * twiddle2;
                    }

                    butterfly4.perform_fft_contiguous_vectorized2_full_trace(
                        &mut row0, &mut row1, &mut row2, &mut row3,
                    );
                }
            });
        }
    });
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub(crate) unsafe fn butterfly_4_vectorized2_mirrored_full_trace_parallel<const N: usize>(
    trace: &RowMajorTraceView<Mersenne31Field, N>,
    twiddles: impl Load,
    num_columns: usize,
    butterfly4: &Butterfly4,
    worker: &Worker,
) {
    // println!("num_columns: {}", num_columns);
    worker.scope(num_columns, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for idx in chunk_start..chunk_start + chunk_size {
                    let tw_idx = idx * 3;

                    let mut row0 = trace.get_row_mut_vectorized(idx + 0 * num_columns);
                    let mut row1 = trace.get_row_mut_vectorized(idx + 1 * num_columns);
                    let mut row2 = trace.get_row_mut_vectorized(idx + 2 * num_columns);
                    let mut row3 = trace.get_row_mut_vectorized(idx + 3 * num_columns);

                    butterfly4.perform_fft_contiguous_vectorized2_full_trace(
                        &mut row0, &mut row1, &mut row2, &mut row3,
                    );

                    let twiddle0 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 0));
                    let twiddle1 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 1));
                    let twiddle2 = Mersenne31ComplexVectorized::constant(twiddles.load(tw_idx + 2));

                    for i in 0..row1.len() {
                        row1[i] = row1[i] * twiddle0;
                        row2[i] = row2[i] * twiddle1;
                        row3[i] = row3[i] * twiddle2;
                    }
                }
            });
        }
    });
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bitreverse_enumeration_inplace;
    use crate::precompute_all_twiddles_for_fft_serial;
    use crate::serial_ct_ntt_natural_to_bitreversed;
    use field::Field;
    use field::Mersenne31Complex;
    use field::Rand;
    use std::alloc::Global;

    #[test]
    fn test_butterfly4() {
        let fft_size: usize = 4;
        let log_n = fft_size.trailing_zeros();
        let mut input = vec![Mersenne31Complex::ONE; fft_size];

        let mut rng = rand::rng();
        for i in 0..input.len() {
            input[i] = Mersenne31Complex::random_element(&mut rng);
        }

        let omegas_bit_reversed: Vec<Mersenne31Complex, Global> =
            precompute_all_twiddles_for_fft_serial::<Mersenne31Complex, Global, false>(fft_size);

        let mut input_ref = input.clone();
        serial_ct_ntt_natural_to_bitreversed(&mut input_ref[..], log_n, &omegas_bit_reversed);
        bitreverse_enumeration_inplace(input_ref.as_mut_slice());

        //test
        let butterfly = Butterfly4::new(FftDirection::Forward);
        unsafe {
            butterfly.perform_fft_contiguous(&mut input[..]);
        }

        println!("input: {:?}", input);
        println!("input_ref: {:?}", input_ref);
        println!("test eq ref: {:?}", input == input_ref);
    }
}
