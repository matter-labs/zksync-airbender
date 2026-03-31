use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_whir_common<MW: MersenneWrapper>(max_fold_steps: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let max_high_powers = if max_fold_steps > 0 {
        1usize << (max_fold_steps - 1)
    } else {
        1
    };
    let mul_pow_gen = MW::mul_assign(quote! { pow }, quote! { set_gen_inv });
    let from_raw_words_i = MW::field_from_reduced_raw_repr(quote! { words[i] });

    let ws_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let ws_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let ws_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let ws_mul_nc_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let ws_add_nc_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let ws_add_nc_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    let mul_gamma_pow = MW::mul_assign(quote! { gamma_pow }, quote! { gamma });

    let field_struct = MW::field_struct();
    let fc_sub_t_b = MW::sub_assign(quote! { t }, quote! { b });
    let fc_mul_t_challenge = MW::mul_assign(quote! { t }, quote! { challenge });
    let fc_mul_t_root = MW::mul_assign_by_base(quote! { t }, quote! { root });
    let fc_add_t_a = MW::add_assign(quote! { t }, quote! { a });
    let fc_add_t_b = MW::add_assign(quote! { t }, quote! { b });
    let fc_mul_t_two_inv = MW::mul_assign_by_base(quote! { t }, quote! { two_inv });

    quote! {
        /// Returns the multiplicative inverse of 2 in the base field.
        #[inline(always)]
        pub fn two_inv() -> #field_struct {
            #field_struct::from_u32_unchecked(2).inverse().unwrap()
        }

        /// Compute tree index from query index for Merkle path verification.
        #[inline(always)]
        pub fn compute_tree_index(
            query_index: usize,
            num_cosets: usize,
            num_cosets_log2: usize,
            coset_tree_size: usize,
        ) -> usize {
            let coset_index = query_index & (num_cosets - 1);
            let internal_index = query_index >> num_cosets_log2;
            if num_cosets == 1 {
                internal_index
            } else {
                let coset_dest = coset_index.reverse_bits()
                    >> (usize::BITS as usize - num_cosets_log2);
                coset_dest * coset_tree_size + internal_index
            }
        }

        #[derive(Clone, Debug)]
        #[allow(dead_code)]
        pub enum WhirVerificationError {
            SumcheckFailed { round: usize },
            FoldAgreementFailed { query: usize },
            MerklePathFailed { query: usize },
        }

        #[inline(always)]
        pub fn verify_whir_sumcheck_step<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
            claim: #quartic_struct,
            round: usize,
        ) -> Result<(#quartic_struct, #quartic_struct), WhirVerificationError> {
            let c0 = read_field_el::<I>();
            let c1 = read_field_el::<I>();
            let c2 = read_field_el::<I>();
            let coeffs = [c0, c1, c2];

            commit_field_els(seed, &coeffs);

            // Check: p(0) + p(1) = c0 + (c0 + c1 + c2) == claim
            let p0 = c0;
            let mut p1 = c0;
            #ws_add_p1_c1;
            #ws_add_p1_c2;
            let mut sum = p0;
            #ws_add_sum_p1;
            if sum != claim {
                return Err(WhirVerificationError::SumcheckFailed { round });
            }

            let mut challenge_buf = [#quartic_zero; 1];
            draw_field_els_into(hasher, seed, &mut challenge_buf);
            let alpha = challenge_buf[0];

            // Horner: c0 + alpha*(c1 + alpha*c2)
            let mut new_claim = c2;
            #ws_mul_nc_alpha;
            #ws_add_nc_c1;
            #ws_mul_nc_alpha;
            #ws_add_nc_c0;

            Ok((new_claim, alpha))
        }

        #[inline(always)]
        pub fn materialize_gamma_powers<const N: usize>(
            gamma: #quartic_struct,
        ) -> [#quartic_struct; N] {
            debug_assert!(N > 1);

            let mut powers: LazyVec<#quartic_struct, N> = LazyVec::new();
            powers.push(#quartic_one);
            let mut i = 1;
            let mut gamma_pow = gamma;
            while i < N - 1 {
                powers.push(gamma_pow);
                #mul_gamma_pow;
                i += 1;
            }
            powers.push(gamma_pow);

            unsafe { powers.into_array() }
        }

        #[inline(always)]
        pub fn fold_coset(
            evals: &[#quartic_struct],
            num_rounds: usize,
            folding_challenges: &[#quartic_struct],
            mut root_inv: #field_struct,
            high_powers_offsets: &[#field_struct],
            two_inv: #field_struct,
            buf_a: &mut [#quartic_struct],
            buf_b: &mut [#quartic_struct],
        ) -> #quartic_struct {
            debug_assert!(num_rounds == 0 || high_powers_offsets.len() >= 1 << (num_rounds - 1));
            let mut round = 0;
            while round < num_rounds {
                let half = 1 << (num_rounds - round - 1);
                let challenge = folding_challenges[round];

                let (src, dst) = if round == 0 {
                    (evals, &mut buf_a[..half])
                } else if round % 2 == 1 {
                    (&buf_a[..half * 2], &mut buf_b[..half])
                } else {
                    (&buf_b[..half * 2], &mut buf_a[..half])
                };

                let mut pair_idx = 0;
                while pair_idx < half {
                    let a = src[pair_idx * 2];
                    let b = src[pair_idx * 2 + 1];

                    let mut t = a;
                    #fc_sub_t_b;
                    #fc_mul_t_challenge;

                    let mut root = root_inv;
                    field_ops::mul_assign(&mut root, &high_powers_offsets[pair_idx]);
                    #fc_mul_t_root;

                    #fc_add_t_a;
                    #fc_add_t_b;
                    #fc_mul_t_two_inv;

                    dst[pair_idx] = t;
                    pair_idx += 1;
                }

                field_ops::square(&mut root_inv);
                round += 1;
            }

            if num_rounds == 0 {
                evals[0]
            } else if num_rounds % 2 == 1 {
                buf_a[0]
            } else {
                buf_b[0]
            }
        }

        pub const MAX_HIGH_POWERS: usize = #max_high_powers;

        #[inline(always)]
        pub fn bitreverse_inplace<T: Copy>(arr: &mut [T]) {
            let n = arr.len();
            if n <= 1 {
                return;
            }
            let log_n = n.trailing_zeros();
            let mut i = 0;
            while i < n {
                let j = (i as u32).reverse_bits().wrapping_shr(32 - log_n) as usize;
                if i < j {
                    let tmp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = tmp;
                }
                i += 1;
            }
        }

        /// Compute bit-reversed high powers of the set-generator inverse for fold_coset.
        /// Returns the number of valid entries written (== 1 << (fold_steps - 1)).
        #[inline(always)]
        pub fn compute_high_powers_offsets(
            fold_steps: usize,
            dst: &mut [#field_struct; MAX_HIGH_POWERS],
        ) -> usize {
            let count = 1usize << (fold_steps - 1);
            let set_gen_inv = #field_struct::TWO_ADICITY_GENERATORS[fold_steps].inverse().unwrap();
            dst[0] = #field_struct::ONE;
            let mut pow = set_gen_inv;
            let mut i = 1;
            while i < count {
                dst[i] = pow;
                #mul_pow_gen;
                i += 1;
            }
            bitreverse_inplace(&mut dst[..count]);
            count
        }

        /// Reconstruct an extension field element from raw u32 words in a buffer.
        #[inline(always)]
        pub fn ext_from_raw_words(words: &[u32]) -> #quartic_struct {
            debug_assert!(words.len() >= EXT_DEGREE);
            let mut coeffs = LazyVec::<#field_struct, EXT_DEGREE>::new();
            let mut i = 0;
            while i < EXT_DEGREE {
                coeffs.push(#from_raw_words_i);
                i += 1;
            }
            unsafe { core::ptr::read(coeffs.as_slice().as_ptr().cast::<#quartic_struct>()) }
        }
    }
}
