use super::*;
use crate::domain_generator_for_size;
use crate::grinded_fft::utils::LoadStore;
use butterfly2::Butterfly2;
use butterfly4::Butterfly4;
use field::FieldLikeVectorized;
use field::Mersenne31ComplexVectorizedInterleaved;
use field::Mersenne31FieldVectorized;
use field::{Mersenne31Complex, Mersenne31Field};
use trace_holder::RowMajorTraceView;

#[derive(Clone, Copy, Debug)]
pub struct Butterfly8 {
    root2: Mersenne31Field,
    direction: FftDirection,
}

impl Butterfly8 {
    #[inline(always)]
    pub fn new(direction: FftDirection) -> Self {
        Self {
            root2: domain_generator_for_size::<Mersenne31Complex>(8 as u64).c0,
            direction,
        }
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn perform_fft_contiguous_vectorized2_full_trace<const N: usize>(
        &self,
        trace: &mut RowMajorTraceView<Mersenne31Field, N>,
    ) {
        let butterfly4 = Butterfly4::new(self.direction);

        let row0 = trace.get_row_mut_vectorized(0);
        let row1 = trace.get_row_mut_vectorized(1);
        let row2 = trace.get_row_mut_vectorized(2);
        let row3 = trace.get_row_mut_vectorized(3);
        let row4 = trace.get_row_mut_vectorized(4);
        let row5 = trace.get_row_mut_vectorized(5);
        let row6 = trace.get_row_mut_vectorized(6);
        let row7 = trace.get_row_mut_vectorized(7);

        //we're going to hardcode a step of mixed radix
        //aka we're going to do the six step algorithm

        // step 1: transpose the input into the scratch (merging with step 2)

        // step 2: column FFTs
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row0, row2, row4, row6);
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row1, row3, row5, row7);

        // step 3: apply twiddle factors
        let tw = Mersenne31FieldVectorized::constant(self.root2);
        for s in row3.iter_mut() {
            *s = (twiddles::rotate_90_vectorized2(*s, self.direction) + *s) * tw;
        }
        for s in row5.iter_mut() {
            *s = twiddles::rotate_90_vectorized2(*s, self.direction);
        }
        for s in row7.iter_mut() {
            *s = (twiddles::rotate_90_vectorized2(*s, self.direction) - *s) * tw;
        }

        // step 4: transpose -- skipped because we're going to do the next FFTs non-contiguously

        // step 5: row FFTs
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row0, row1);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row2, row3);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row4, row5);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row6, row7);

        // step 6: copy data to the output. we don't need to transpose, because we skipped the step 4 transpose
        for i in 0..row1.len() {
            let scratch0 = [row2[i], row4[i], row6[i]];
            let scratch1 = [row1[i], row3[i], row5[i]];
            row1[i] = scratch0[0];
            row2[i] = scratch0[1];
            row3[i] = scratch0[2];
            row4[i] = scratch1[0];
            row5[i] = scratch1[1];
            row6[i] = scratch1[2];
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        8
    }
    #[inline(always)]
    pub fn fft_direction(&self) -> FftDirection {
        self.direction
    }

    #[inline(always)]
    pub unsafe fn perform_fft_contiguous(&self, mut buffer: impl LoadStore<Mersenne31Complex>) {
        let butterfly4 = Butterfly4::new(self.direction);

        //we're going to hardcode a step of mixed radix
        //aka we're going to do the six step algorithm

        // step 1: transpose the input into the scratch
        let mut scratch0 = [
            buffer.load(0),
            buffer.load(2),
            buffer.load(4),
            buffer.load(6),
        ];
        let mut scratch1 = [
            buffer.load(1),
            buffer.load(3),
            buffer.load(5),
            buffer.load(7),
        ];

        // step 2: column FFTs
        butterfly4.perform_fft_contiguous(&mut scratch0);
        butterfly4.perform_fft_contiguous(&mut scratch1);

        // step 3: apply twiddle factors
        scratch1[1] = (twiddles::rotate_90(scratch1[1], self.direction) + scratch1[1]) * self.root2;
        scratch1[2] = twiddles::rotate_90(scratch1[2], self.direction);
        scratch1[3] = (twiddles::rotate_90(scratch1[3], self.direction) - scratch1[3]) * self.root2;

        // step 4: transpose -- skipped because we're going to do the next FFTs non-contiguously

        // step 5: row FFTs
        for i in 0..4 {
            Butterfly2::perform_fft_strided(&mut scratch0[i], &mut scratch1[i]);
        }

        // step 6: copy data to the output. we don't need to transpose, because we skipped the step 4 transpose
        for i in 0..4 {
            buffer.store(scratch0[i], i);
        }
        for i in 0..4 {
            buffer.store(scratch1[i], i + 4);
        }
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn perform_fft_strided_vectorized2_full_trace(
        &self,
        row0: &mut [Mersenne31ComplexVectorizedInterleaved],
        row1: &mut [Mersenne31ComplexVectorizedInterleaved],
        row2: &mut [Mersenne31ComplexVectorizedInterleaved],
        row3: &mut [Mersenne31ComplexVectorizedInterleaved],
        row4: &mut [Mersenne31ComplexVectorizedInterleaved],
        row5: &mut [Mersenne31ComplexVectorizedInterleaved],
        row6: &mut [Mersenne31ComplexVectorizedInterleaved],
        row7: &mut [Mersenne31ComplexVectorizedInterleaved],
    ) {
        let butterfly4 = Butterfly4::new(self.direction);

        //we're going to hardcode a step of mixed radix
        //aka we're going to do the six step algorithm

        // step 1: transpose the input into the scratch (merging with step 2)

        // step 2: column FFTs
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row0, row2, row4, row6);
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row1, row3, row5, row7);

        // step 3: apply twiddle factors
        let tw = Mersenne31FieldVectorized::constant(self.root2);
        for s in row3.iter_mut() {
            *s = (twiddles::rotate_90_vectorized2(*s, self.direction) + *s) * tw;
        }
        for s in row5.iter_mut() {
            *s = twiddles::rotate_90_vectorized2(*s, self.direction);
        }
        for s in row7.iter_mut() {
            *s = (twiddles::rotate_90_vectorized2(*s, self.direction) - *s) * tw;
        }

        // step 4: transpose -- skipped because we're going to do the next FFTs non-contiguously

        // step 5: row FFTs
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row0, row1);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row2, row3);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row4, row5);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row6, row7);

        // step 6: copy data to the output. we don't need to transpose, because we skipped the step 4 transpose
        for i in 0..row1.len() {
            let scratch0 = [row2[i], row4[i], row6[i]];
            let scratch1 = [row1[i], row3[i], row5[i]];
            row1[i] = scratch0[0];
            row2[i] = scratch0[1];
            row3[i] = scratch0[2];
            row4[i] = scratch1[0];
            row5[i] = scratch1[1];
            row6[i] = scratch1[2];
        }
    }
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
    fn test_butterfly8() {
        let fft_size: usize = 8;
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
        let butterfly = Butterfly8::new(FftDirection::Forward);
        println!("root2: {:?}", butterfly.root2);
        unsafe {
            butterfly.perform_fft_contiguous(&mut input[..]);
        }

        // println!("input: {:?}", input);
        // println!("input_ref: {:?}", input_ref);
        println!("test eq ref: {:?}", input == input_ref);
    }
}
