use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_transcript_helpers<MW: MersenneWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let field_from_raw = MW::field_from_reduced_raw_repr(quote! { I::read_word() });
    let field_from_u32 = MW::field_from_u32_with_reduction(quote! { w });

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
        pub fn draw_field_els_into(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
            dst: &mut [#quartic_struct],
        ) {
            let n = dst.len();
            let padded = (n * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            assert!(padded <= DRAW_BUF_CAPACITY, "draw buffer too small");

            let mut words = LazyVec::<u32, DRAW_BUF_CAPACITY>::new();
            unsafe {
                words.set_len(padded);
                Blake2sTranscript::draw_randomness_using_hasher(hasher, seed, words.as_mut_slice());
            }

            for (i, chunk) in words.as_slice()[..n * EXT_DEGREE]
                .chunks_exact(EXT_DEGREE)
                .enumerate()
            {
                let mut arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
                for &w in chunk {
                    arr.push(#field_from_u32);
                }
                dst[i] = unsafe { core::ptr::read(arr.as_slice().as_ptr().cast::<#quartic_struct>()) };
            }
        }
    }
}
