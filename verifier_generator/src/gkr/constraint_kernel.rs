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

/// Generate a data-driven constraint kernel using const descriptor arrays + loops.
///
/// Three term types:
/// - Constant: `result += coeff * challenge_powers[pow]`
/// - Linear:   `result += coeff * challenge_powers[pow] * evals[idx][j]`
/// - Quadratic: `result += coeff * challenge_powers[pow] * evals[idx_a][j] * evals[idx_b][j]`
pub fn generate_constraint_kernel<MW: MersenneWrapper, F: PrimeField>(
    rel: &NoFieldMaxQuadraticConstraintsGKRRelation,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let quartic_zero = MW::quartic_zero();
    let quartic_struct = MW::quartic_struct();
    let field_struct = MW::field_struct();

    // Collect constant terms: (coeff_mont, pow)
    let const_coeffs: Vec<u32> = rel
        .constants
        .iter()
        .map(|&(c, _)| coeff_to_internal_repr::<F>(c))
        .collect();
    let const_pows: Vec<usize> = rel.constants.iter().map(|&(_, p)| p).collect();
    let num_const = const_coeffs.len();

    // Collect linear terms flattened: (coeff_mont, pow, eval_idx)
    // Group by eval address: each group shares the same evals[idx][j] load
    // But for simplicity with const arrays, flatten completely.
    let mut lin_coeffs: Vec<u32> = Vec::new();
    let mut lin_pows: Vec<usize> = Vec::new();
    let mut lin_evals: Vec<usize> = Vec::new();
    for (addr, terms) in &rel.linear_terms {
        let idx = addr_to_idx(addr, input_sorted_addrs);
        for &(coeff, pow) in terms.iter() {
            lin_coeffs.push(coeff_to_internal_repr::<F>(coeff));
            lin_pows.push(pow);
            lin_evals.push(idx);
        }
    }
    let num_lin = lin_coeffs.len();

    // Collect quadratic terms flattened: (coeff_mont, pow, idx_a, idx_b)
    // Group by (addr_a, addr_b) pair: each group shares the same product load.
    // Use group descriptors to avoid redundant multiplies.
    // quad_groups: (idx_a, idx_b, term_start, term_count)
    // quad_terms: (coeff_mont, pow)
    let mut quad_groups: Vec<(usize, usize, usize, usize)> = Vec::new();
    let mut quad_coeffs: Vec<u32> = Vec::new();
    let mut quad_pows: Vec<usize> = Vec::new();
    for ((addr_a, addr_b), terms) in &rel.quadratic_terms {
        let idx_a = addr_to_idx(addr_a, input_sorted_addrs);
        let idx_b = addr_to_idx(addr_b, input_sorted_addrs);
        let start = quad_coeffs.len();
        for &(coeff, pow) in terms.iter() {
            quad_coeffs.push(coeff_to_internal_repr::<F>(coeff));
            quad_pows.push(pow);
        }
        quad_groups.push((idx_a, idx_b, start, terms.len()));
    }
    let num_quad_groups = quad_groups.len();
    let qg_a: Vec<usize> = quad_groups.iter().map(|g| g.0).collect();
    let qg_b: Vec<usize> = quad_groups.iter().map(|g| g.1).collect();
    let qg_start: Vec<usize> = quad_groups.iter().map(|g| g.2).collect();
    let qg_count: Vec<usize> = quad_groups.iter().map(|g| g.3).collect();
    let num_quad_terms = quad_coeffs.len();

    let mul_by_base = MW::mul_assign_by_base(
        quote! { t },
        quote! { #field_struct::from_reduced_raw_repr(coeff) },
    );
    let add_to_result = MW::add_assign(quote! { result }, quote! { t });

    // Linear: multiply t by loaded val
    let mul_by_val = MW::mul_assign(quote! { t }, quote! { val });

    // Quadratic: multiply prod = va * vb, then t by prod
    let mul_prod = MW::mul_assign(quote! { prod }, quote! { vb });
    let mul_by_prod = MW::mul_assign(quote! { t }, quote! { prod });

    let mut body = TokenStream::new();

    body.extend(quote! {
        let mut result: #quartic_struct = #quartic_zero;
    });

    // Constant terms
    if num_const > 0 {
        body.extend(quote! {
            {
                const CK_CONST: [(u32, usize); #num_const] = [
                    #( (#const_coeffs, #const_pows), )*
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

    // Linear terms
    if num_lin > 0 {
        body.extend(quote! {
            {
                const CK_LIN: [(u32, usize, usize); #num_lin] = [
                    #( (#lin_coeffs, #lin_pows, #lin_evals), )*
                ];
                let mut _i: usize = 0;
                while _i < #num_lin {
                    let (coeff, pow, eval_idx) = CK_LIN[_i];
                    let val = evals.get_unchecked(eval_idx)[j];
                    let mut t: #quartic_struct = *challenge_powers.get_unchecked(pow);
                    #mul_by_base;
                    #mul_by_val;
                    #add_to_result;
                    _i += 1;
                }
            }
        });
    }

    // Quadratic terms (grouped by address pair to share the product)
    if num_quad_groups > 0 {
        body.extend(quote! {
            {
                const CK_QUAD_GROUPS: [(usize, usize, usize, usize); #num_quad_groups] = [
                    #( (#qg_a, #qg_b, #qg_start, #qg_count), )*
                ];
                const CK_QUAD_TERMS: [(u32, usize); #num_quad_terms] = [
                    #( (#quad_coeffs, #quad_pows), )*
                ];
                let mut _g: usize = 0;
                while _g < #num_quad_groups {
                    let (idx_a, idx_b, term_start, term_count) = CK_QUAD_GROUPS[_g];
                    let va = evals.get_unchecked(idx_a)[j];
                    let vb = evals.get_unchecked(idx_b)[j];
                    let mut prod = va;
                    #mul_prod;
                    let mut _t: usize = 0;
                    while _t < term_count {
                        let (coeff, pow) = CK_QUAD_TERMS[term_start + _t];
                        let mut t: #quartic_struct = *challenge_powers.get_unchecked(pow);
                        #mul_by_base;
                        #mul_by_prod;
                        #add_to_result;
                        _t += 1;
                    }
                    _g += 1;
                }
            }
        });
    }

    body.extend(quote! { result });
    body
}
