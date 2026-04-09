use std::collections::BTreeMap;

use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation;
use prover::field::PrimeField;

use super::addr_to_idx;
use super::coeff_to_internal_repr;

pub fn generate_constraint_kernel<MW: MersenneWrapper, F: PrimeField>(
    rel: &NoFieldMaxQuadraticConstraintsGKRRelation,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let quartic_zero = MW::quartic_zero();
    let quartic_struct = MW::quartic_struct();
    let field_struct = MW::field_struct();

    let mut const_by_pow: BTreeMap<usize, Vec<u32>> = BTreeMap::new();
    for &(c, pow) in &rel.constants {
        const_by_pow
            .entry(pow)
            .or_default()
            .push(coeff_to_internal_repr::<F>(c));
    }
    let mut const_summed_coeffs: Vec<u32> = Vec::new();
    let mut const_summed_pows: Vec<usize> = Vec::new();
    for (pow, coeffs) in &const_by_pow {
        let mut sum = F::ZERO;
        for &c in coeffs {
            sum.add_assign(&F::from_reduced_raw_repr(c));
        }
        let s = sum.as_u32_raw_repr_reduced();
        if s != 0 {
            const_summed_coeffs.push(s);
            const_summed_pows.push(*pow);
        }
    }
    let num_const = const_summed_coeffs.len();

    let mut lin_by_pow: BTreeMap<usize, Vec<(u32, usize)>> = BTreeMap::new();
    for (addr, terms) in &rel.linear_terms {
        let idx = addr_to_idx(addr, input_sorted_addrs);
        for &(coeff, pow) in terms.iter() {
            lin_by_pow
                .entry(pow)
                .or_default()
                .push((coeff_to_internal_repr::<F>(coeff), idx));
        }
    }
    let mut lin_group_pows: Vec<usize> = Vec::new();
    let mut lin_group_starts: Vec<usize> = Vec::new();
    let mut lin_group_counts: Vec<usize> = Vec::new();
    let mut lin_term_coeffs: Vec<u32> = Vec::new();
    let mut lin_term_evals: Vec<usize> = Vec::new();
    for (pow, terms) in &lin_by_pow {
        lin_group_pows.push(*pow);
        lin_group_starts.push(lin_term_coeffs.len());
        lin_group_counts.push(terms.len());
        for &(coeff, idx) in terms {
            lin_term_coeffs.push(coeff);
            lin_term_evals.push(idx);
        }
    }
    let num_lin_groups = lin_group_pows.len();
    let num_lin_terms = lin_term_coeffs.len();

    let mut quad_by_pow: BTreeMap<usize, Vec<(u32, usize, usize)>> = BTreeMap::new();
    for ((addr_a, addr_b), terms) in &rel.quadratic_terms {
        let idx_a = addr_to_idx(addr_a, input_sorted_addrs);
        let idx_b = addr_to_idx(addr_b, input_sorted_addrs);
        for &(coeff, pow) in terms.iter() {
            quad_by_pow.entry(pow).or_default().push((
                coeff_to_internal_repr::<F>(coeff),
                idx_a,
                idx_b,
            ));
        }
    }
    let mut quad_group_pows: Vec<usize> = Vec::new();
    let mut quad_group_starts: Vec<usize> = Vec::new();
    let mut quad_group_counts: Vec<usize> = Vec::new();
    let mut quad_term_coeffs: Vec<u32> = Vec::new();
    let mut quad_term_a: Vec<usize> = Vec::new();
    let mut quad_term_b: Vec<usize> = Vec::new();
    for (pow, terms) in &quad_by_pow {
        quad_group_pows.push(*pow);
        quad_group_starts.push(quad_term_coeffs.len());
        quad_group_counts.push(terms.len());
        for &(coeff, ia, ib) in terms {
            quad_term_coeffs.push(coeff);
            quad_term_a.push(ia);
            quad_term_b.push(ib);
        }
    }
    let num_quad_groups = quad_group_pows.len();
    let num_quad_terms = quad_term_coeffs.len();

    let mul_by_base = MW::mul_assign_by_base(
        quote! { t },
        quote! { #field_struct::from_reduced_raw_repr(coeff) },
    );
    let add_to_result = MW::add_assign(quote! { result }, quote! { t });

    let mul_val_by_coeff = MW::mul_assign_by_base(
        quote! { val },
        quote! { #field_struct::from_reduced_raw_repr(coeff) },
    );
    let add_to_inner = MW::add_assign(quote! { inner_sum }, quote! { val });
    let mul_inner_by_cp = MW::mul_assign(quote! { t }, quote! { inner_sum });

    let mul_prod = MW::mul_assign(quote! { prod }, quote! { vb });
    let mul_prod_by_coeff = MW::mul_assign_by_base(
        quote! { prod },
        quote! { #field_struct::from_reduced_raw_repr(coeff) },
    );
    let add_prod_to_inner = MW::add_assign(quote! { inner_sum }, quote! { prod });
    let mul_inner_by_cp_q = MW::mul_assign(quote! { t }, quote! { inner_sum });

    let mut body = TokenStream::new();

    body.extend(quote! {
        let mut result: #quartic_struct = #quartic_zero;
    });

    if num_const > 0 {
        body.extend(quote! {
            {
                const CK_CONST: [(u32, usize); #num_const] = [
                    #( (#const_summed_coeffs, #const_summed_pows), )*
                ];
                let mut _i: usize = 0;
                while _i < #num_const {
                    let (coeff, pow) = CK_CONST[_i];
                    let mut t: #quartic_struct = *challenge_powers.get_unchecked(pow);
                    #mul_by_base;
                    #add_to_result;
                    _i += 1;
                }
            }
        });
    }

    if num_lin_groups > 0 {
        body.extend(quote! {
            {
                const CK_LIN_GROUPS: [(usize, usize, usize); #num_lin_groups] = [
                    #( (#lin_group_pows, #lin_group_starts, #lin_group_counts), )*
                ];
                const CK_LIN_TERMS: [(u32, usize); #num_lin_terms] = [
                    #( (#lin_term_coeffs, #lin_term_evals), )*
                ];
                let mut _g: usize = 0;
                while _g < #num_lin_groups {
                    let (pow, term_start, term_count) = CK_LIN_GROUPS[_g];
                    let mut inner_sum: #quartic_struct = #quartic_zero;
                    let mut _t: usize = 0;
                    while _t < term_count {
                        let (coeff, eval_idx) = CK_LIN_TERMS[term_start + _t];
                        let mut val = evals.get_unchecked(eval_idx)[j];
                        #mul_val_by_coeff;
                        #add_to_inner;
                        _t += 1;
                    }
                    let mut t: #quartic_struct = *challenge_powers.get_unchecked(pow);
                    #mul_inner_by_cp;
                    #add_to_result;
                    _g += 1;
                }
            }
        });
    }

    if num_quad_groups > 0 {
        body.extend(quote! {
            {
                const CK_QUAD_GROUPS: [(usize, usize, usize); #num_quad_groups] = [
                    #( (#quad_group_pows, #quad_group_starts, #quad_group_counts), )*
                ];
                const CK_QUAD_TERMS: [(u32, usize, usize); #num_quad_terms] = [
                    #( (#quad_term_coeffs, #quad_term_a, #quad_term_b), )*
                ];
                let mut _g: usize = 0;
                while _g < #num_quad_groups {
                    let (pow, term_start, term_count) = CK_QUAD_GROUPS[_g];
                    let mut inner_sum: #quartic_struct = #quartic_zero;
                    let mut _t: usize = 0;
                    while _t < term_count {
                        let (coeff, idx_a, idx_b) = CK_QUAD_TERMS[term_start + _t];
                        let va = evals.get_unchecked(idx_a)[j];
                        let vb = evals.get_unchecked(idx_b)[j];
                        let mut prod = va;
                        #mul_prod;
                        #mul_prod_by_coeff;
                        #add_prod_to_inner;
                        _t += 1;
                    }
                    let mut t: #quartic_struct = *challenge_powers.get_unchecked(pow);
                    #mul_inner_by_cp_q;
                    #add_to_result;
                    _g += 1;
                }
            }
        });
    }

    body.extend(quote! { result });
    body
}
