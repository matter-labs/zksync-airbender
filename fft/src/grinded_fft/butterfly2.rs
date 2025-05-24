use super::*;
use crate::grinded_fft::utils::LoadStore;
use field::Mersenne31Complex;
use field::Mersenne31ComplexVectorizedInterleaved;

pub struct Butterfly2 {
    direction: FftDirection,
}
impl Butterfly2 {
    #[inline(always)]
    pub fn new(direction: FftDirection) -> Self {
        Self { direction }
    }
    #[inline(always)]
    pub unsafe fn perform_fft_strided(left: &mut Mersenne31Complex, right: &mut Mersenne31Complex) {
        let temp = *left + *right;

        *right = *left - *right;
        *left = temp;
    }

    #[inline(always)]
    pub unsafe fn perform_fft_strided_vectorized2_full_trace(
        left_slice: &mut [Mersenne31ComplexVectorizedInterleaved],
        right_slice: &mut [Mersenne31ComplexVectorizedInterleaved],
    ) {
        for (left, right) in left_slice.iter_mut().zip(right_slice.iter_mut()) {
            let temp = *left + *right;
            *right = *left - *right;
            *left = temp;
        }
    }
    #[inline(always)]
    pub unsafe fn perform_fft_contiguous(&self, mut buffer: impl LoadStore<Mersenne31Complex>) {
        let value0 = buffer.load(0);
        let value1 = buffer.load(1);
        buffer.store(value0 + value1, 0);
        buffer.store(value0 - value1, 1);
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        2
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
    use crate::precompute_all_twiddles_for_fft_serial;
    use crate::serial_ct_ntt_natural_to_bitreversed;
    use field::Field;
    use field::Mersenne31Complex;
    use field::Rand;
    use std::alloc::Global;

    #[test]
    fn test_butterfly2() {
        let fft_size: usize = 2;
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
        let butterfly = Butterfly2::new(FftDirection::Forward);
        unsafe {
            butterfly.perform_fft_contiguous(&mut input[..]);
        }

        println!("test eq ref: {:?}", input == input_ref);
    }
}
