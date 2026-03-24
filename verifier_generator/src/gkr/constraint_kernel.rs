use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation;
use prover::field::PrimeField;

use super::addr_to_idx;

fn coeff_to_internal_repr<F: PrimeField>(coeff: u32) -> u32 {
    F::from_u32_with_reduction(coeff).as_u32_raw_repr_reduced()
}

pub fn generate_constraint_kernel<MW: MersenneWrapper, F: PrimeField>(
    rel: &NoFieldMaxQuadraticConstraintsGKRRelation,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let quartic_zero = MW::quartic_zero();
    let mut body = quote! {
        let mut result = #quartic_zero;
    };

    for &(coeff, pow) in &rel.constants {
        let mont = coeff_to_internal_repr::<F>(coeff);
        let field_coeff = MW::field_new(quote! { #mont });
        let mul_by_base = MW::mul_assign_by_base(quote! { t }, field_coeff);
        let add_to_result = MW::add_assign(quote! { result }, quote! { t });
        body.extend(quote! {
            {
                let mut t = unsafe { *challenge_powers.get_unchecked(#pow) };
                #mul_by_base;
                #add_to_result;
            }
        });
    }

    for (addr, terms) in &rel.linear_terms {
        let idx = addr_to_idx(addr, input_sorted_addrs);
        let mut term_body = TokenStream::new();
        for &(coeff, pow) in terms.iter() {
            let mont = coeff_to_internal_repr::<F>(coeff);
            let field_coeff = MW::field_new(quote! { #mont });
            let mul_by_base = MW::mul_assign_by_base(quote! { t }, field_coeff);
            let mul_by_val = MW::mul_assign(quote! { t }, quote! { val });
            let add_to_result = MW::add_assign(quote! { result }, quote! { t });
            term_body.extend(quote! {
                {
                    let mut t = unsafe { *challenge_powers.get_unchecked(#pow) };
                    #mul_by_base;
                    #mul_by_val;
                    #add_to_result;
                }
            });
        }
        body.extend(quote! {
            {
                let val = unsafe { evals.get_unchecked(#idx) }[j];
                #term_body
            }
        });
    }

    for ((addr_a, addr_b), terms) in &rel.quadratic_terms {
        let idx_a = addr_to_idx(addr_a, input_sorted_addrs);
        let idx_b = addr_to_idx(addr_b, input_sorted_addrs);
        let mul_prod = MW::mul_assign(quote! { prod }, quote! { vb });
        let mut term_body = TokenStream::new();
        for &(coeff, pow) in terms.iter() {
            let mont = coeff_to_internal_repr::<F>(coeff);
            let field_coeff = MW::field_new(quote! { #mont });
            let mul_by_base = MW::mul_assign_by_base(quote! { t }, field_coeff);
            let mul_by_prod = MW::mul_assign(quote! { t }, quote! { prod });
            let add_to_result = MW::add_assign(quote! { result }, quote! { t });
            term_body.extend(quote! {
                {
                    let mut t = unsafe { *challenge_powers.get_unchecked(#pow) };
                    #mul_by_base;
                    #mul_by_prod;
                    #add_to_result;
                }
            });
        }
        body.extend(quote! {
            {
                let va = unsafe { evals.get_unchecked(#idx_a) }[j];
                let vb = unsafe { evals.get_unchecked(#idx_b) }[j];
                let mut prod = va;
                #mul_prod;
                #term_body
            }
        });
    }

    body.extend(quote! { result });
    body
}
