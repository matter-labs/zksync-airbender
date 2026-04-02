use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_transcript_helpers<MW: MersenneWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let field_from_raw = MW::field_from_reduced_raw_repr(quote! { I::read_reduced_field_element(#field_struct::ORDER) });
    let field_from_u32 = MW::field_from_raw_repr_with_reduction(quote! { w });

    quote! {
        #[inline(always)]
        pub fn read_field_el<I: NonDeterminismSource>() -> #quartic_struct {
            let mut words = LazyVec::<#field_struct, EXT_DEGREE>::new();
            for _ in 0..EXT_DEGREE {
                words.push(#field_from_raw);
            }
            unsafe { core::ptr::read(words.as_slice().as_ptr().cast::<#quartic_struct>()) }
        }

        #[inline(always)]
        pub fn read_field_els<I: NonDeterminismSource>(dst: &mut [#quartic_struct]) {
            for el in dst.iter_mut() {
                *el = read_field_el::<I>();
            }
        }

        #[inline(always)]
        pub fn commit_field_els(seed: &mut Seed, els: &[#quartic_struct]) {
            let total = els.len() * EXT_DEGREE;
            let as_u32 = unsafe { core::slice::from_raw_parts(els.as_ptr().cast::<u32>(), total) };
            Blake2sTranscript::commit_with_seed(seed, as_u32);
        }

        #[inline(always)]
        pub fn draw_field_els_into<const BUF_CAP: usize>(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
            dst: &mut [#quartic_struct],
        ) {
            let n = dst.len();
            let padded = (n * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            debug_assert!(padded <= BUF_CAP, "draw buffer too small");

            let mut words = LazyVec::<u32, BUF_CAP>::new();
            unsafe {
                words.set_len(padded);
                Blake2sTranscript::draw_randomness_using_hasher(hasher, seed, words.as_mut_slice());
            }

            let mut i = 0;
            while i < n {
                let base = i * EXT_DEGREE;
                let mut arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
                let mut k = 0;
                while k < EXT_DEGREE {
                    let w = unsafe { *words.get_unchecked(base + k) };
                    arr.push(#field_from_u32);
                    k += 1;
                }
                unsafe { *dst.get_unchecked_mut(i) = core::ptr::read(arr.as_slice().as_ptr().cast::<#quartic_struct>()) };
                i += 1;
            }
        }

        /// Draw a single extension field element from the transcript.
        #[inline(always)]
        pub fn draw_single_field_el(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
        ) -> #quartic_struct {
            let mut buf = LazyVec::<#quartic_struct, 1>::new();
            unsafe { buf.set_len(1); }
            draw_field_els_into::<BLAKE2S_DIGEST_SIZE_U32_WORDS>(hasher, seed, buf.as_mut_slice());
            *buf.get(0)
        }
    }
}
