use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_transcript_helpers<MW: MersenneWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    quote! {
        #[inline(always)]
        pub fn read_reduced_field_el<I: NonDeterminismSource>() -> u32 {
            I::read_reduced_field_element(#field_struct::ORDER)
        }

        #[inline(always)]
        pub fn read_field_el<I: NonDeterminismSource>() -> #quartic_struct {
            ext_from_nds::<#field_struct, #quartic_struct, I>()
        }

        #[inline(always)]
        pub fn read_field_els<I: NonDeterminismSource>(dst: &mut [#quartic_struct]) {
            let mut i = 0;
            while i < dst.len() {
                dst[i] = read_field_el::<I>();
                i += 1;
            }
        }

        #[inline(always)]
        pub fn draw_field_els_into<const BUF_CAP: usize>(
            ts: &mut TranscriptState,
            dst: &mut [#quartic_struct],
        ) {
            let n = dst.len();
            let padded = (n * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            debug_assert!(padded <= BUF_CAP, "draw buffer too small");

            let mut words = LazyVec::<u32, BUF_CAP>::new();
            unsafe {
                words.set_len(padded);
                ts.draw_raw(words.as_mut_slice());
            }

            let mut i = 0;
            while i < n {
                let base = i * EXT_DEGREE;
                let raw = unsafe { (words.as_slice().as_ptr().add(base) as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
                unsafe {
                    *dst.get_unchecked_mut(i) = ext_from_raw_words::<#field_struct, #quartic_struct>(raw);
                }
                i += 1;
            }
        }

        #[inline(always)]
        pub fn draw_single_field_el(
            ts: &mut TranscriptState,
        ) -> #quartic_struct {
            let mut words = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
            unsafe {
                words.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS);
                ts.draw_raw(words.as_mut_slice());
            }
            let raw = unsafe { words.as_array::<E::DEGREE>() };
            ext_from_raw_words::<#field_struct, #quartic_struct>(raw)
        }
    }
}
