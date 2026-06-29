use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;

pub fn generate_transcript_helpers<MW: FieldWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    quote! {
        #[inline(always)]
        pub fn read_reduced_field_el<I: NonDeterminismSource>(nd_source: &mut I) -> u32 {
            nd_source.read_reduced_field_element(#field_struct::ORDER)
        }

        #[inline(always)]
        pub fn read_field_el<I: NonDeterminismSource>(nd_source: &mut I) -> #quartic_struct {
            ext_from_nds::<#field_struct, #quartic_struct, I>(nd_source)
        }

        #[inline(always)]
        pub fn read_field_els<I: NonDeterminismSource>(dst: &mut [#quartic_struct], nd_source: &mut I) {
            let mut i = 0;
            while i < dst.len() {
                dst[i] = read_field_el::<I>(nd_source);
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
            assert!(padded <= BUF_CAP, "draw buffer too small");

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
                    *dst.get_unchecked_mut(i) = ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw);
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
            let raw = unsafe { words.as_array::<EXT_DEGREE>() };
            ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw)
        }

        /// Variant of [`draw_field_els_into`] used immediately after a `read_and_verify_pow`:
        /// the first drawn word was consumed by the PoW, so we draw one extra word and skip it.
        /// The drawn word count matches the prover's `draw_random_field_els_with_pow` exactly.
        #[inline(always)]
        pub fn draw_field_els_into_after_pow<const BUF_CAP: usize>(
            ts: &mut TranscriptState,
            dst: &mut [#quartic_struct],
        ) {
            let n = dst.len();
            let padded = (n * EXT_DEGREE + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            assert!(padded <= BUF_CAP, "draw buffer too small");

            let mut words = LazyVec::<u32, BUF_CAP>::new();
            unsafe {
                words.set_len(padded);
                ts.draw_raw(words.as_mut_slice());
            }

            let mut i = 0;
            while i < n {
                // skip first word used for PoW
                let base = 1 + i * EXT_DEGREE;
                let raw = unsafe { (words.as_slice().as_ptr().add(base) as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
                unsafe {
                    *dst.get_unchecked_mut(i) = ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw);
                }
                i += 1;
            }
        }

        /// Variant of [`draw_single_field_el`] used immediately after a `read_and_verify_pow`:
        /// the first drawn word was consumed by the PoW and is skipped. One digest worth of words
        /// (8) covers the skipped word plus a single EXT_DEGREE=4 element.
        #[inline(always)]
        pub fn draw_single_field_el_after_pow(
            ts: &mut TranscriptState,
        ) -> #quartic_struct {
            let mut words = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
            unsafe {
                words.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS);
                ts.draw_raw(words.as_mut_slice());
            }
            // skip first word used for PoW
            let raw = unsafe { (words.as_slice().as_ptr().add(1) as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
            ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw)
        }
    }
}
