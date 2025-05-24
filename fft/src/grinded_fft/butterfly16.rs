use super::*;
use crate::grinded_fft::utils::LoadStore;
use butterfly2::Butterfly2;
use butterfly4::Butterfly4;
use butterfly8::Butterfly8;
use field::FieldLikeVectorized;
use field::Mersenne31ComplexVectorizedInterleaved;
use field::{Mersenne31Complex, Mersenne31Field};
use trace_holder::RowMajorTraceView;

#[derive(Clone, Copy, Debug)]
pub struct Butterfly16 {
    butterfly8: Butterfly8,
    twiddle1: Mersenne31Complex,
    twiddle2: Mersenne31Complex,
    twiddle3: Mersenne31Complex,
}

impl Butterfly16 {
    #[inline(always)]
    pub fn new(direction: FftDirection) -> Self {
        Self {
            butterfly8: Butterfly8::new(direction),
            twiddle1: twiddles::compute_twiddle(1, 16, direction),
            twiddle2: twiddles::compute_twiddle(2, 16, direction),
            twiddle3: twiddles::compute_twiddle(3, 16, direction),
        }
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn perform_fft_contiguous_vectorized2_full_trace<const N: usize>(
        &self,
        trace: &mut RowMajorTraceView<Mersenne31Field, N>,
    ) {
        let butterfly4 = Butterfly4::new(self.fft_direction());

        let row0 = trace.get_row_mut_vectorized(0);
        let row1 = trace.get_row_mut_vectorized(1);
        let row2 = trace.get_row_mut_vectorized(2);
        let row3 = trace.get_row_mut_vectorized(3);
        let row4 = trace.get_row_mut_vectorized(4);
        let row5 = trace.get_row_mut_vectorized(5);
        let row6 = trace.get_row_mut_vectorized(6);
        let row7 = trace.get_row_mut_vectorized(7);
        let row8 = trace.get_row_mut_vectorized(8);
        let row9 = trace.get_row_mut_vectorized(9);
        let row10 = trace.get_row_mut_vectorized(10);
        let row11 = trace.get_row_mut_vectorized(11);
        let row12 = trace.get_row_mut_vectorized(12);
        let row13 = trace.get_row_mut_vectorized(13);
        let row14 = trace.get_row_mut_vectorized(14);
        let row15 = trace.get_row_mut_vectorized(15);

        // step 2: column FFTs
        self.butterfly8.perform_fft_strided_vectorized2_full_trace(
            row0, row2, row4, row6, row8, row10, row12, row14,
        );
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row1, row5, row9, row13);
        butterfly4.perform_fft_contiguous_vectorized2_full_trace(row15, row3, row7, row11);

        // step 3: apply twiddle factors
        let twiddle1_conj = *self.twiddle1.clone().conjugate();
        let tw1 = Mersenne31ComplexVectorizedInterleaved::constant(self.twiddle1);
        let tw1_conj = Mersenne31ComplexVectorizedInterleaved::constant(twiddle1_conj);
        for (v0, v1) in row5.iter_mut().zip(row3.iter_mut()) {
            *v0 = *v0 * tw1;
            *v1 = *v1 * tw1_conj;
        }

        let twiddle2_conj = *self.twiddle2.clone().conjugate();
        let tw2 = Mersenne31ComplexVectorizedInterleaved::constant(self.twiddle2);
        let tw2_conj = Mersenne31ComplexVectorizedInterleaved::constant(twiddle2_conj);
        for (v0, v1) in row9.iter_mut().zip(row7.iter_mut()) {
            *v0 = *v0 * tw2;
            *v1 = *v1 * tw2_conj;
        }

        let twiddle3_conj = *self.twiddle3.clone().conjugate();
        let tw3 = Mersenne31ComplexVectorizedInterleaved::constant(self.twiddle3);
        let tw3_conj = Mersenne31ComplexVectorizedInterleaved::constant(twiddle3_conj);
        for (v0, v1) in row13.iter_mut().zip(row11.iter_mut()) {
            *v0 = *v0 * tw3;
            *v1 = *v1 * tw3_conj;
        }

        // step 4: cross FFTs
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row1, row15);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row5, row3);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row9, row7);
        Butterfly2::perform_fft_strided_vectorized2_full_trace(row13, row11);

        // apply the butterfly 4 twiddle factor, which is just a rotation
        for v in row15.iter_mut() {
            *v = twiddles::rotate_90_vectorized2(*v, self.fft_direction());
        }
        for v in row3.iter_mut() {
            *v = twiddles::rotate_90_vectorized2(*v, self.fft_direction());
        }
        for v in row7.iter_mut() {
            *v = twiddles::rotate_90_vectorized2(*v, self.fft_direction());
        }
        for v in row11.iter_mut() {
            *v = twiddles::rotate_90_vectorized2(*v, self.fft_direction());
        }

        //step 5: copy/add/subtract data back to buffer
        for i in 0..row0.len() {
            let t0 = row0[i] + row1[i];
            let t1 = row2[i] + row5[i];
            let t2 = row4[i] + row9[i];
            let t3 = row6[i] + row13[i];
            let t4 = row8[i] + row15[i];
            let t5 = row10[i] + row3[i];
            let t6 = row12[i] + row7[i];
            let t7 = row14[i] + row11[i];
            let t8 = row0[i] - row1[i];
            let t9 = row2[i] - row5[i];
            let t10 = row4[i] - row9[i];
            let t11 = row6[i] - row13[i];
            let t12 = row8[i] - row15[i];
            let t13 = row10[i] - row3[i];
            let t14 = row12[i] - row7[i];
            let t15 = row14[i] - row11[i];
            row0[i] = t0;
            row1[i] = t1;
            row2[i] = t2;
            row3[i] = t3;
            row4[i] = t4;
            row5[i] = t5;
            row6[i] = t6;
            row7[i] = t7;
            row8[i] = t8;
            row9[i] = t9;
            row10[i] = t10;
            row11[i] = t11;
            row12[i] = t12;
            row13[i] = t13;
            row14[i] = t14;
            row15[i] = t15;
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        16
    }
    #[inline(always)]
    pub fn fft_direction(&self) -> FftDirection {
        self.butterfly8.fft_direction()
    }

    #[inline(always)]
    pub unsafe fn perform_fft_contiguous(&self, mut buffer: impl LoadStore<Mersenne31Complex>) {
        let butterfly4 = Butterfly4::new(self.fft_direction());

        // we're going to hardcode a step of split radix
        // step 1: copy and reorder the  input into the scratch
        let mut scratch_evens = [
            buffer.load(0),
            buffer.load(2),
            buffer.load(4),
            buffer.load(6),
            buffer.load(8),
            buffer.load(10),
            buffer.load(12),
            buffer.load(14),
        ];

        let mut scratch_odds_n1 = [
            buffer.load(1),
            buffer.load(5),
            buffer.load(9),
            buffer.load(13),
        ];
        let mut scratch_odds_n3 = [
            buffer.load(15),
            buffer.load(3),
            buffer.load(7),
            buffer.load(11),
        ];

        // step 2: column FFTs
        self.butterfly8.perform_fft_contiguous(&mut scratch_evens);
        butterfly4.perform_fft_contiguous(&mut scratch_odds_n1);
        butterfly4.perform_fft_contiguous(&mut scratch_odds_n3);

        // step 3: apply twiddle factors
        let twiddle1_conj = *self.twiddle1.clone().conjugate();
        scratch_odds_n1[1] = scratch_odds_n1[1] * self.twiddle1;
        scratch_odds_n3[1] = scratch_odds_n3[1] * twiddle1_conj;

        let twiddle2_conj = *self.twiddle2.clone().conjugate();
        scratch_odds_n1[2] = scratch_odds_n1[2] * self.twiddle2;
        scratch_odds_n3[2] = scratch_odds_n3[2] * twiddle2_conj;

        let twiddle3_conj = *self.twiddle3.clone().conjugate();
        scratch_odds_n1[3] = scratch_odds_n1[3] * self.twiddle3;
        scratch_odds_n3[3] = scratch_odds_n3[3] * twiddle3_conj;

        // step 4: cross FFTs
        Butterfly2::perform_fft_strided(&mut scratch_odds_n1[0], &mut scratch_odds_n3[0]);
        Butterfly2::perform_fft_strided(&mut scratch_odds_n1[1], &mut scratch_odds_n3[1]);
        Butterfly2::perform_fft_strided(&mut scratch_odds_n1[2], &mut scratch_odds_n3[2]);
        Butterfly2::perform_fft_strided(&mut scratch_odds_n1[3], &mut scratch_odds_n3[3]);

        // apply the butterfly 4 twiddle factor, which is just a rotation
        scratch_odds_n3[0] = twiddles::rotate_90(scratch_odds_n3[0], self.fft_direction());
        scratch_odds_n3[1] = twiddles::rotate_90(scratch_odds_n3[1], self.fft_direction());
        scratch_odds_n3[2] = twiddles::rotate_90(scratch_odds_n3[2], self.fft_direction());
        scratch_odds_n3[3] = twiddles::rotate_90(scratch_odds_n3[3], self.fft_direction());

        //step 5: copy/add/subtract data back to buffer
        buffer.store(scratch_evens[0] + scratch_odds_n1[0], 0);
        buffer.store(scratch_evens[1] + scratch_odds_n1[1], 1);
        buffer.store(scratch_evens[2] + scratch_odds_n1[2], 2);
        buffer.store(scratch_evens[3] + scratch_odds_n1[3], 3);
        buffer.store(scratch_evens[4] + scratch_odds_n3[0], 4);
        buffer.store(scratch_evens[5] + scratch_odds_n3[1], 5);
        buffer.store(scratch_evens[6] + scratch_odds_n3[2], 6);
        buffer.store(scratch_evens[7] + scratch_odds_n3[3], 7);
        buffer.store(scratch_evens[0] - scratch_odds_n1[0], 8);
        buffer.store(scratch_evens[1] - scratch_odds_n1[1], 9);
        buffer.store(scratch_evens[2] - scratch_odds_n1[2], 10);
        buffer.store(scratch_evens[3] - scratch_odds_n1[3], 11);
        buffer.store(scratch_evens[4] - scratch_odds_n3[0], 12);
        buffer.store(scratch_evens[5] - scratch_odds_n3[1], 13);
        buffer.store(scratch_evens[6] - scratch_odds_n3[2], 14);
        buffer.store(scratch_evens[7] - scratch_odds_n3[3], 15);
    }

    #[inline(always)]
    pub fn get_inplace_scratch_len(&self) -> usize {
        0
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
    fn test_butterfly16() {
        let fft_size: usize = 16;
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
        let butterfly = Butterfly16::new(FftDirection::Forward);
        unsafe {
            butterfly.perform_fft_contiguous(&mut input[..]);
        }

        // println!("input: {:?}", input);
        // println!("input_ref: {:?}", input_ref);
        println!("test eq ref: {:?}", input == input_ref);
    }
}
