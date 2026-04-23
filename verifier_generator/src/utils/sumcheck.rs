use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_sumcheck_helpers<MW: MersenneWrapper>() -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mul_t_eq = MW::mul_assign(quote! { t }, quote! { *unsafe { eq.get_unchecked(i) } });
    let add_result_t = MW::add_assign(quote! { result }, quote! { t });

    let sub_f0_c = MW::sub_assign(quote! { f0 }, quote! { c });
    let mul_left_f0 = MW::mul_assign(quote! { left }, quote! { f0 });
    let mul_right_f1 = MW::mul_assign(quote! { right }, quote! { f1 });

    quote! {
        #[inline(always)]
        pub fn dot_eq<const N: usize>(values: &[#quartic_struct; N], eq: &[#quartic_struct; N]) -> #quartic_struct {
            let mut result = #quartic_zero;
            for i in 0..N {
                let mut t = unsafe { *values.get_unchecked(i) };
                #mul_t_eq;
                #add_result_t;
            }
            result
        }

        #[inline(always)]
        pub fn make_eq_poly<const M: usize, const N: usize>(
            challenges: &[#quartic_struct; M],
            buf: &mut LazyVec<#quartic_struct, N>,
        ) {
            assert_eq!(N, 1 << M);
            unsafe { buf.set_unchecked(0, #quartic_one) };
            let mut size = 1usize;
            let mut idx = M;
            for _ in 0..M {
                idx -= 1;
                let c = unsafe { *challenges.get_unchecked(idx) };
                let f1 = c;
                let mut f0 = #quartic_one;
                #sub_f0_c;
                let half = size;

                for i in (0..half).rev() {
                    let prev = unsafe { *buf.get_unchecked(i) };
                    let mut left = prev;
                    let mut right = prev;
                    #mul_left_f0;
                    #mul_right_f1;
                    unsafe {
                        buf.set_unchecked(i, left);
                        buf.set_unchecked(i + half, right);
                    }
                }
                size *= 2;
            }
            unsafe { buf.set_len(N) };
        }
    }
}
