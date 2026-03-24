use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_whir_common<MW: MersenneWrapper>() -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();

    let ws_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let ws_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let ws_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let ws_mul_nc_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let ws_add_nc_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let ws_add_nc_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    let add_p2_a = MW::add_assign(quote! { p2 }, quote! { a });
    let add_p2_b1 = MW::add_assign(quote! { p2 }, quote! { b });
    let add_p2_b2 = MW::add_assign(quote! { p2 }, quote! { b });
    let sub_p2_c1 = MW::sub_assign(quote! { p2 }, quote! { c });
    let sub_p2_c2 = MW::sub_assign(quote! { p2 }, quote! { c });
    let sub_p2_c3 = MW::sub_assign(quote! { p2 }, quote! { c });
    let sub_p2_c4 = MW::sub_assign(quote! { p2 }, quote! { c });
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
            #add_p2_b1;
            #add_p2_b2;
            #sub_p2_c1;
            #sub_p2_c2;
            #sub_p2_c3;
            #sub_p2_c4;

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
    }
}
