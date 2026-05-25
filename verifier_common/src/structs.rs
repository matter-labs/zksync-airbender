pub use crate::transcript::{Blake2sTranscript, CommitBuf, Seed, TranscriptState};
use core::mem::MaybeUninit;

pub struct FoldBuffers<E: Copy, const N: usize> {
    buf_a: [MaybeUninit<E>; N],
    buf_b: [MaybeUninit<E>; N],
}

impl<E: Copy, const N: usize> FoldBuffers<E, N> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            buf_a: [const { MaybeUninit::uninit() }; N],
            buf_b: [const { MaybeUninit::uninit() }; N],
        }
    }

    #[inline(always)]
    pub unsafe fn src_dst(
        &mut self,
        round: usize,
        src_len: usize,
        dst_len: usize,
    ) -> (&[E], &mut [E]) {
        if round % 2 == 0 {
            let src = core::slice::from_raw_parts(self.buf_b.as_ptr().cast::<E>(), src_len);
            let dst = core::slice::from_raw_parts_mut(self.buf_a.as_mut_ptr().cast::<E>(), dst_len);
            (src, dst)
        } else {
            let src = core::slice::from_raw_parts(self.buf_a.as_ptr().cast::<E>(), src_len);
            let dst = core::slice::from_raw_parts_mut(self.buf_b.as_mut_ptr().cast::<E>(), dst_len);
            (src, dst)
        }
    }

    #[inline(always)]
    pub unsafe fn dst_a(&mut self, len: usize) -> &mut [E] {
        core::slice::from_raw_parts_mut(self.buf_a.as_mut_ptr().cast::<E>(), len)
    }

    #[inline(always)]
    pub unsafe fn result(&self, num_rounds: usize) -> E {
        if num_rounds % 2 == 1 {
            *self.buf_a.get_unchecked(0).assume_init_ref()
        } else {
            *self.buf_b.get_unchecked(0).assume_init_ref()
        }
    }
}

pub struct BitSource<'a> {
    u32_values: &'a [u32],
    index: usize,
}

impl<'a> BitSource<'a> {
    pub fn new(u32_values: &'a [u32]) -> Self {
        Self {
            u32_values,
            index: 0,
        }
    }
}

impl<'a> Iterator for BitSource<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.u32_values.len() * (u32::BITS as usize) {
            return None;
        }

        let word_index = self.index / (u32::BITS as usize);
        let bit_index = self.index % (u32::BITS as usize);
        let word = unsafe { core::ptr::read_volatile(&self.u32_values[word_index]) };
        let bit = (word >> bit_index) & 1;
        self.index += 1;

        Some(bit as usize)
    }
}

pub fn assemble_query_index(
    num_bits: usize,
    bit_source: &mut impl Iterator<Item = usize>,
) -> usize {
    // assemble as LE
    debug_assert!(num_bits <= usize::BITS as usize);
    let mut result = 0usize;
    for i in 0..num_bits {
        result |= unsafe { bit_source.next().unwrap_unchecked() } << i;
    }

    result
}

pub fn bitreverse_for_bitlength(num: u32, bitlength: u32) -> u32 {
    let shift = u32::BITS - bitlength;
    num.reverse_bits() >> shift
}

#[inline(always)]
pub fn ext_from_nds<
    F: field::PrimeField,
    E: field::FieldExtension<F>,
    I: non_determinism_source::NonDeterminismSource,
>(
    nd_source: &mut I,
) -> E {
    // layout of E should be [F; E::DEGREE]
    debug_assert_eq!(
        core::mem::size_of::<E>(),
        core::mem::size_of::<F>() * E::DEGREE
    );

    use field::FixedArrayConvertible;

    unsafe {
        let mut coeffs = core::mem::MaybeUninit::<E::Coeffs>::uninit();
        let dst = E::Coeffs::project_uninit(&mut coeffs);
        let mut i = 0;
        while i < E::DEGREE {
            dst.get_unchecked_mut(i).write(F::from_reduced_raw_repr(
                nd_source.read_reduced_field_element(F::CHARACTERISTICS),
            ));
            i += 1;
        }
        E::from_coeffs(coeffs.assume_init())
    }
}

#[inline(always)]
pub fn ext_from_raw_words<F: field::PrimeField, E: field::FieldExtension<F>, const N: usize>(
    words: &[u32; N],
) -> E {
    assert_eq!(N, E::DEGREE);

    debug_assert_eq!(
        core::mem::size_of::<E>(),
        core::mem::size_of::<F>() * E::DEGREE
    );

    use field::FixedArrayConvertible;

    unsafe {
        let mut coeffs = core::mem::MaybeUninit::<E::Coeffs>::uninit();
        let dst = E::Coeffs::project_uninit(&mut coeffs);
        let mut i = 0;
        while i < E::DEGREE {
            dst.get_unchecked_mut(i)
                .write(F::from_raw_repr_with_reduction(words[i]));
            i += 1;
        }
        E::from_coeffs(coeffs.assume_init())
    }
}
