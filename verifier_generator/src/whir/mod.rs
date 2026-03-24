use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_whir_common<MW: MersenneWrapper>() -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let ws_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let ws_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let ws_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let ws_mul_nc_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let ws_add_nc_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let ws_add_nc_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    let mul_gamma_pow = MW::mul_assign(quote! { gamma_pow }, quote! { gamma });
    let mul_term_claim = MW::mul_assign(quote! { term }, quote! { claim_i });
    let add_batched_term = MW::add_assign(quote! { batched }, quote! { term });

    let field_struct = MW::field_struct();
    let fc_sub_t_b = MW::sub_assign(quote! { t }, quote! { b });
    let fc_mul_t_challenge = MW::mul_assign(quote! { t }, quote! { challenge });
    let fc_mul_t_root = MW::mul_assign_by_base(quote! { t }, quote! { root });
    let fc_add_t_a = MW::add_assign(quote! { t }, quote! { a });
    let fc_add_t_b = MW::add_assign(quote! { t }, quote! { b });
    let fc_mul_t_two_inv = MW::mul_assign_by_base(quote! { t }, quote! { two_inv });

    let add_p2_a = MW::add_assign(quote! { p2 }, quote! { a });
    let add_p2_b = MW::add_assign(quote! { p2 }, quote! { b });
    let sub_p2_c = MW::sub_assign(quote! { p2 }, quote! { c });
    let sub_p1_a = MW::sub_assign(quote! { p1 }, quote! { a });
    let sub_p1_p2 = MW::sub_assign(quote! { p1 }, quote! { p2 });
    let mul_inner_alpha1 = MW::mul_assign(quote! { inner }, quote! { alpha });
    let add_inner_p1 = MW::add_assign(quote! { inner }, quote! { p1 });
    let mul_inner_alpha2 = MW::mul_assign(quote! { inner }, quote! { alpha });
    let add_inner_a = MW::add_assign(quote! { inner }, quote! { a });

    quote! {
        #[derive(Clone, Debug)]
        pub enum WhirVerificationError {
            SumcheckFailed { round: usize },
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
        pub fn lagrange_eval_3pt(a: #quartic_struct, b: #quartic_struct, c: #quartic_struct, alpha: #quartic_struct) -> #quartic_struct {
            // p2 = 2a + 2b - 4c
            let mut p2 = a;
            #add_p2_a;
            #add_p2_b;
            #add_p2_b;
            #sub_p2_c;
            #sub_p2_c;
            #sub_p2_c;
            #sub_p2_c;

            let mut p1 = b;
            #sub_p1_a;
            #sub_p1_p2;

            let mut inner = p2;
            #mul_inner_alpha1;
            #add_inner_p1;
            #mul_inner_alpha2;
            #add_inner_a;
            inner
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
        pub fn batch_claims<const NUM_CLAIMS: usize, const CAP: usize>(
            claims: &LazyVec<#quartic_struct, CAP>,
            gamma_powers: &[#quartic_struct; NUM_CLAIMS],
        ) -> #quartic_struct {
            debug_assert!(NUM_CLAIMS > 0);
            debug_assert!(NUM_CLAIMS <= CAP);
            let mut batched = *claims.get(0);
            let mut i = 1;
            while i < NUM_CLAIMS {
                let claim_i = *claims.get(i);
                let mut term = gamma_powers[i];
                #mul_term_claim;
                #add_batched_term;
                i += 1;
            }
            batched
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
    }
}
