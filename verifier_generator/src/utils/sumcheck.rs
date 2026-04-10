use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_sumcheck_helpers<MW: MersenneWrapper>() -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let dot_mul_t_eq = MW::mul_assign(quote! { t }, quote! { *unsafe { eq.get_unchecked(i) } });
    let dot_add_result_t = MW::add_assign(quote! { result }, quote! { t });

    let eq_sub_f0_c = MW::sub_assign(quote! { f0 }, quote! { c });
    let eq_mul_left_f0 = MW::mul_assign(quote! { left }, quote! { f0 });
    let eq_mul_right_f1 = MW::mul_assign(quote! { right }, quote! { f1 });

    quote! {
        #[inline(always)]
        pub fn dot_eq<const N: usize>(values: &[#quartic_struct; N], eq: &[#quartic_struct; N]) -> #quartic_struct {
            let mut result = #quartic_zero;
            for i in 0..N {
                let mut t = unsafe { *values.get_unchecked(i) };
                #dot_mul_t_eq;
                #dot_add_result_t;
            }
            result
        }

        #[inline(always)]
        pub fn make_eq_poly<const N: usize>(
            challenges: &[#quartic_struct; N],
            buf: &mut LazyVec<#quartic_struct, { 1 << N }>,
        ) {
            unsafe { buf.set_unchecked(0, #quartic_one) };
            let mut size = 1usize;
            let mut idx = N;
            for _ in 0..N {
                idx -= 1;
                let c = unsafe { *challenges.get_unchecked(idx) };
                let f1 = c;
                let mut f0 = #quartic_one;
                #eq_sub_f0_c;
                let half = size;

                for i in (0..half).rev() {
                    let prev = unsafe { *buf.get_unchecked(i) };
                    let mut left = prev;
                    let mut right = prev;
                    #eq_mul_left_f0;
                    #eq_mul_right_f1;
                    unsafe {
                        buf.set_unchecked(i, left);
                        buf.set_unchecked(i + half, right);
                    }
                }
                size *= 2;
            }
            unsafe { buf.set_len(1 << N) };
        }
    }
}
