use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::cs::definitions::gkr::{
    NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
};
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation};
use prover::field::PrimeField;

use super::addr_to_idx;
use super::constraint_kernel::generate_constraint_kernel;

fn coeff_to_internal_repr<F: PrimeField>(coeff: u32) -> u32 {
    F::from_u32_with_reduction(coeff).as_u32_raw_repr_reduced()
}

fn coeff64_to_internal_repr<F: PrimeField>(coeff: u64) -> u32 {
    let reduced = (coeff % (F::CHARACTERISTICS as u64)) as u32;
    F::from_u32_with_reduction(reduced).as_u32_raw_repr_reduced()
}

pub fn generate_layer_compute_claim<MW: MersenneWrapper>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    output_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_compute_claim", layer_idx);
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mut body = quote! {
        let mut current_batch = #quartic_one;
    };

    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let gates: Vec<_> = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .collect();
    let num_gates = gates.len();
    let mut first_contributing = true;

    for (gate_idx, gate) in gates.into_iter().enumerate() {
        let is_last = gate_idx == num_gates - 1;
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceConstraintsMaxQuadratic { .. } => {
                if !is_last {
                    body.extend(quote! {
                        #mul_batch;
                    });
                }
            }
            R::LinearBaseFieldRelation { output, .. }
            | R::MaxQuadratic { output, .. }
            | R::Copy { output, .. }
            | R::InitialGrandProductFromCaches { output, .. }
            | R::TrivialProduct { output, .. }
            | R::MaskIntoIdentityProduct { output, .. }
            | R::UnbalancedGrandProductWithCache { output, .. }
            | R::MaterializeSingleLookupInput { output, .. }
            | R::MaterializedVectorLookupInput { output, .. } => {
                let out_idx = addr_to_idx(output, output_sorted_addrs);
                let mul_t = MW::mul_assign(quote! { t }, quote! { claim });
                let advance = if is_last {
                    quote! {}
                } else {
                    quote! { #mul_batch; }
                };
                if first_contributing {
                    first_contributing = false;
                    body.extend(quote! {
                        let combined = {
                            let bc = current_batch;
                            #advance
                            let claim = output_claims.get(#out_idx);
                            let mut t = bc;
                            #mul_t;
                            t
                        };
                        let mut combined = combined;
                    });
                } else {
                    let add_combined = MW::add_assign(quote! { combined }, quote! { t });
                    body.extend(quote! {
                        {
                            let bc = current_batch;
                            #advance
                            let claim = output_claims.get(#out_idx);
                            let mut t = bc;
                            #mul_t;
                            #add_combined;
                        }
                    });
                }
            }
            R::AggregateLookupRationalPair { output, .. }
            | R::LookupPairFromBaseInputs { output, .. }
            | R::LookupPairFromMaterializedBaseInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
            | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
            | R::LookupPairFromVectorInputs { output, .. }
            | R::LookupPairFromMaterializedVectorInputs { output, .. }
            | R::LookupPairFromCachedVectorInputs { output, .. }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
            | R::LookupWithCachedDensAndSetup { output, .. }
            | R::LookupFromMaterializedVectorInputWithSetup { output, .. } => {
                let o0 = addr_to_idx(&output[0], output_sorted_addrs);
                let o1 = addr_to_idx(&output[1], output_sorted_addrs);
                let mul_t0 = MW::mul_assign(quote! { t0 }, quote! { c0 });
                let mul_t1 = MW::mul_assign(quote! { t1 }, quote! { c1 });
                let advance = if is_last {
                    quote! {}
                } else {
                    quote! { #mul_batch; }
                };
                if first_contributing {
                    first_contributing = false;
                    let add_t1 = MW::add_assign(quote! { t0 }, quote! { t1 });
                    body.extend(quote! {
                        let combined = {
                            let bc0 = current_batch;
                            #mul_batch;
                            let bc1 = current_batch;
                            #advance
                            let c0 = output_claims.get(#o0);
                            let c1 = output_claims.get(#o1);
                            let mut t0 = bc0;
                            #mul_t0;
                            let mut t1 = bc1;
                            #mul_t1;
                            #add_t1;
                            t0
                        };
                        let mut combined = combined;
                    });
                } else {
                    let add_t0 = MW::add_assign(quote! { combined }, quote! { t0 });
                    let add_t1 = MW::add_assign(quote! { combined }, quote! { t1 });
                    body.extend(quote! {
                        {
                            let bc0 = current_batch;
                            #mul_batch;
                            let bc1 = current_batch;
                            #advance
                            let c0 = output_claims.get(#o0);
                            let c1 = output_claims.get(#o1);
                            let mut t0 = bc0;
                            #mul_t0;
                            #add_t0;
                            let mut t1 = bc1;
                            #mul_t1;
                            #add_t1;
                        }
                    });
                }
            }
        }
    }

    body.extend(quote! { combined });

    let quartic_struct = MW::quartic_struct();
    quote! {
        #[inline(always)]
        unsafe fn #fn_name(
            output_claims: &LazyVec<#quartic_struct, GKR_ADDRS>,
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            #body
        }
    }
}

pub fn generate_layer_final_step_accumulator<MW: MersenneWrapper, F: PrimeField>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    input_sorted_addrs: &[GKRAddress],
    max_pow: usize,
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_final_step_accumulator", layer_idx);
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let field_one = MW::field_one();

    let quartic_struct = MW::quartic_struct();

    let mut body = quote! {
        let mut acc = [#quartic_zero; 2];
        let mut current_batch = #quartic_one;
    };

    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let gates = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter());

    for gate in gates {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceConstraintsMaxQuadratic { input } => {
                let kernel_body = generate_constraint_kernel::<MW, F>(input, input_sorted_addrs);
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let val = { #kernel_body };
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::Copy { input, .. } => {
                let i = addr_to_idx(input, input_sorted_addrs);
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let val = unsafe { evals.get_unchecked(#i) }[j];
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::LinearBaseFieldRelation { input, .. } => {
                let const_mont = coeff_to_internal_repr::<F>(input.constant);
                let const_field = MW::field_new(quote! { #const_mont });
                let mut val_computation = quote! {
                    let mut val = #quartic_struct::from_base(#const_field);
                };
                for &(coeff, ref addr) in input.linear_terms.iter() {
                    let idx = addr_to_idx(addr, input_sorted_addrs);
                    let mont = coeff_to_internal_repr::<F>(coeff);
                    let field_coeff = MW::field_new(quote! { #mont });
                    let mul_coeff = MW::mul_assign_by_base(quote! { term }, field_coeff);
                    let add_term = MW::add_assign(quote! { val }, quote! { term });
                    val_computation.extend(quote! {
                        let mut term = unsafe { evals.get_unchecked(#idx) }[j];
                        #mul_coeff;
                        #add_term;
                    });
                }
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            #val_computation
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::MaxQuadratic { input, .. } => {
                let const_mont = coeff64_to_internal_repr::<F>(input.constant);
                let const_field = MW::field_new(quote! { #const_mont });
                let mut val_computation = quote! {
                    let mut val = #quartic_struct::from_base(#const_field);
                };
                for (addr_a, inner_terms) in input.quadratic_terms.iter() {
                    let ia = addr_to_idx(addr_a, input_sorted_addrs);
                    let mut inner_sum = quote! {
                        let mut inner = #quartic_zero;
                    };
                    for &(coeff, ref addr_b) in inner_terms.iter() {
                        let ib = addr_to_idx(addr_b, input_sorted_addrs);
                        let mont = coeff64_to_internal_repr::<F>(coeff);
                        let field_coeff = MW::field_new(quote! { #mont });
                        let mul_coeff = MW::mul_assign_by_base(quote! { t }, field_coeff);
                        let add_t = MW::add_assign(quote! { inner }, quote! { t });
                        inner_sum.extend(quote! {
                            let mut t = unsafe { evals.get_unchecked(#ib) }[j];
                            #mul_coeff;
                            #add_t;
                        });
                    }
                    let mul_a = MW::mul_assign(quote! { inner }, quote! { a_val });
                    let add_inner = MW::add_assign(quote! { val }, quote! { inner });
                    val_computation.extend(quote! {
                        {
                            #inner_sum
                            let a_val = unsafe { evals.get_unchecked(#ia) }[j];
                            #mul_a;
                            #add_inner;
                        }
                    });
                }
                for &(coeff, ref addr) in input.linear_terms.iter() {
                    let idx = addr_to_idx(addr, input_sorted_addrs);
                    let mont = coeff64_to_internal_repr::<F>(coeff);
                    let field_coeff = MW::field_new(quote! { #mont });
                    let mul_coeff = MW::mul_assign_by_base(quote! { lt }, field_coeff);
                    let add_lt = MW::add_assign(quote! { val }, quote! { lt });
                    val_computation.extend(quote! {
                        let mut lt = unsafe { evals.get_unchecked(#idx) }[j];
                        #mul_coeff;
                        #add_lt;
                    });
                }
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            #val_computation
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::InitialGrandProductFromCaches { input, .. } | R::TrivialProduct { input, .. } => {
                let i0 = addr_to_idx(&input[0], input_sorted_addrs);
                let i1 = addr_to_idx(&input[1], input_sorted_addrs);
                let mul_ab = MW::mul_assign(quote! { val }, quote! { vb });
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = unsafe { evals.get_unchecked(#i0) }[j];
                            let vb = unsafe { evals.get_unchecked(#i1) }[j];
                            #mul_ab;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::MaskIntoIdentityProduct { input, mask, .. } => {
                let i = addr_to_idx(input, input_sorted_addrs);
                let m = addr_to_idx(mask, input_sorted_addrs);
                let sub_one = MW::sub_assign_base(quote! { val }, field_one.clone());
                let mul_mask = MW::mul_assign(quote! { val }, quote! { mask_val });
                let add_one = MW::add_assign_base(quote! { val }, field_one.clone());
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = unsafe { evals.get_unchecked(#i) }[j];
                            let mask_val = unsafe { evals.get_unchecked(#m) }[j];
                            #sub_one;
                            #mul_mask;
                            #add_one;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::AggregateLookupRationalPair { input, .. } => {
                let i00 = addr_to_idx(&input[0][0], input_sorted_addrs);
                let i01 = addr_to_idx(&input[0][1], input_sorted_addrs);
                let i10 = addr_to_idx(&input[1][0], input_sorted_addrs);
                let i11 = addr_to_idx(&input[1][1], input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let a = unsafe { evals.get_unchecked(#i00) }[j];
                        let b = unsafe { evals.get_unchecked(#i01) }[j];
                        let c = unsafe { evals.get_unchecked(#i10) }[j];
                        let d = unsafe { evals.get_unchecked(#i11) }[j];
                    },
                    // num = a*d + c*b
                    |mw_mul, mw_add| {
                        let mul_ad = mw_mul(quote! { num }, quote! { d });
                        let mul_cb = mw_mul(quote! { cb_tmp }, quote! { b });
                        let add_cb = mw_add(quote! { num }, quote! { cb_tmp });
                        quote! {
                            let mut num = a;
                            #mul_ad;
                            let mut cb_tmp = c;
                            #mul_cb;
                            #add_cb;
                            num
                        }
                    },
                    // den = b*d
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d });
                        quote! {
                            let mut den = b;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::LookupPairFromMaterializedBaseInputs { input, .. }
            | R::LookupPairFromMaterializedVectorInputs { input, .. }
            | R::LookupPairFromCachedVectorInputs { input, .. } => {
                let i0 = addr_to_idx(&input[0], input_sorted_addrs);
                let i1 = addr_to_idx(&input[1], input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let mut b_g = unsafe { evals.get_unchecked(#i0) }[j];
                        let mut d_g = unsafe { evals.get_unchecked(#i1) }[j];
                    },
                    |_, mw_add| {
                        let add_gamma_b =
                            mw_add(quote! { b_g }, quote! { lookup_additive_challenge });
                        let add_gamma_d =
                            mw_add(quote! { d_g }, quote! { lookup_additive_challenge });
                        let add_bd = mw_add(quote! { num }, quote! { d_g });
                        quote! {
                            #add_gamma_b;
                            #add_gamma_d;
                            let mut num = b_g;
                            #add_bd;
                            num
                        }
                    },
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d_g });
                        quote! {
                            let mut den = b_g;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. } => {
                let i_in = addr_to_idx(input, input_sorted_addrs);
                let s0 = addr_to_idx(&setup[0], input_sorted_addrs);
                let s1 = addr_to_idx(&setup[1], input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let mut b_g = unsafe { evals.get_unchecked(#i_in) }[j];
                        let mut d_g = unsafe { evals.get_unchecked(#s1) }[j];
                        let mut cb_g = unsafe { evals.get_unchecked(#s0) }[j];
                    },
                    |mw_mul, mw_add| {
                        let add_gamma_b =
                            mw_add(quote! { b_g }, quote! { lookup_additive_challenge });
                        let add_gamma_d =
                            mw_add(quote! { d_g }, quote! { lookup_additive_challenge });
                        let mul_cb = mw_mul(quote! { cb_g }, quote! { b_g });
                        let sub_cb = MW::sub_assign(quote! { num }, quote! { cb_g });
                        quote! {
                            #add_gamma_b;
                            #add_gamma_d;
                            #mul_cb;
                            let mut num = d_g;
                            #sub_cb;
                            num
                        }
                    },
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d_g });
                        quote! {
                            let mut den = b_g;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::LookupUnbalancedPairWithMaterializedBaseInputs {
                input, remainder, ..
            }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs {
                input, remainder, ..
            } => {
                let i0 = addr_to_idx(&input[0], input_sorted_addrs);
                let i1 = addr_to_idx(&input[1], input_sorted_addrs);
                let r = addr_to_idx(remainder, input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let a = unsafe { evals.get_unchecked(#i0) }[j];
                        let b = unsafe { evals.get_unchecked(#i1) }[j];
                        let mut d_g = unsafe { evals.get_unchecked(#r) }[j];
                    },
                    |mw_mul, mw_add| {
                        let add_gamma =
                            mw_add(quote! { d_g }, quote! { lookup_additive_challenge });
                        let mul_ad = mw_mul(quote! { num }, quote! { d_g });
                        let add_b = mw_add(quote! { num }, quote! { b });
                        quote! {
                            #add_gamma;
                            let mut num = a;
                            #mul_ad;
                            #add_b;
                            num
                        }
                    },
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d_g });
                        quote! {
                            let mut den = b;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::LookupWithCachedDensAndSetup { input, setup, .. } => {
                // a/(b+γ) - c/(d+γ) -> num = a*(d+γ) - c*(b+γ), den = (b+γ)*(d+γ)
                let i0 = addr_to_idx(&input[0], input_sorted_addrs);
                let i1 = addr_to_idx(&input[1], input_sorted_addrs);
                let s0 = addr_to_idx(&setup[0], input_sorted_addrs);
                let s1 = addr_to_idx(&setup[1], input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let a = unsafe { evals.get_unchecked(#i0) }[j];
                        let mut b = unsafe { evals.get_unchecked(#i1) }[j];
                        let c = unsafe { evals.get_unchecked(#s0) }[j];
                        let mut d = unsafe { evals.get_unchecked(#s1) }[j];
                    },
                    |mw_mul, mw_add| {
                        let add_gamma_b =
                            mw_add(quote! { b }, quote! { lookup_additive_challenge });
                        let add_gamma_d =
                            mw_add(quote! { d }, quote! { lookup_additive_challenge });
                        let mul_ad = mw_mul(quote! { ad }, quote! { d });
                        let mul_cb = mw_mul(quote! { cb }, quote! { b });
                        let sub_cb = MW::sub_assign(quote! { ad }, quote! { cb });
                        quote! {
                            #add_gamma_b;
                            #add_gamma_d;
                            let mut ad = a;
                            #mul_ad;
                            let mut cb = c;
                            #mul_cb;
                            #sub_cb;
                            ad
                        }
                    },
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d });
                        quote! {
                            let mut den = b;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
                // 1/(b+γ) - c/(d+γ) -> num = (d+γ) - c*(b+γ), den = (b+γ)*(d+γ)
                let ib = addr_to_idx(input, input_sorted_addrs);
                let s0 = addr_to_idx(&setup[0], input_sorted_addrs);
                let s1 = addr_to_idx(&setup[1], input_sorted_addrs);
                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        let mut b = unsafe { evals.get_unchecked(#ib) }[j];
                        let c = unsafe { evals.get_unchecked(#s0) }[j];
                        let mut d = unsafe { evals.get_unchecked(#s1) }[j];
                    },
                    |mw_mul, mw_add| {
                        let add_gamma_b =
                            mw_add(quote! { b }, quote! { lookup_additive_challenge });
                        let add_gamma_d =
                            mw_add(quote! { d }, quote! { lookup_additive_challenge });
                        let mul_cb = mw_mul(quote! { cb }, quote! { b });
                        let sub_cb = MW::sub_assign(quote! { d }, quote! { cb });
                        quote! {
                            #add_gamma_b;
                            #add_gamma_d;
                            let mut cb = c;
                            #mul_cb;
                            #sub_cb;
                            d
                        }
                    },
                    |mw_mul, _| {
                        let mul_bd = mw_mul(quote! { den }, quote! { d });
                        quote! {
                            let mut den = b;
                            #mul_bd;
                            den
                        }
                    },
                );
            }
            R::UnbalancedGrandProductWithCache { scalar, input, .. } => {
                let is = addr_to_idx(scalar, input_sorted_addrs);
                let ii = addr_to_idx(input, input_sorted_addrs);
                let mul_si = MW::mul_assign(quote! { val }, quote! { vi });
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = unsafe { evals.get_unchecked(#is) }[j];
                            let vi = unsafe { evals.get_unchecked(#ii) }[j];
                            #mul_si;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::MaterializeSingleLookupInput { input, .. } => {
                let const_mont = coeff_to_internal_repr::<F>(input.input.constant);
                let const_field = MW::field_new(quote! { #const_mont });
                let mut val_computation = quote! {
                    let mut val = #quartic_struct::from_base(#const_field);
                };
                for &(coeff, ref addr) in input.input.linear_terms.iter() {
                    let idx = addr_to_idx(addr, input_sorted_addrs);
                    let mont = coeff_to_internal_repr::<F>(coeff);
                    let field_coeff = MW::field_new(quote! { #mont });
                    let mul_coeff = MW::mul_assign_by_base(quote! { term }, field_coeff);
                    let add_term = MW::add_assign(quote! { val }, quote! { term });
                    val_computation.extend(quote! {
                        let mut term = unsafe { evals.get_unchecked(#idx) }[j];
                        #mul_coeff;
                        #add_term;
                    });
                }
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            #val_computation
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::MaterializedVectorLookupInput { input, .. } => {
                let mut val_computation = quote! {
                    let mut val = #quartic_zero;
                };
                for (col_idx, col) in input.columns.iter().enumerate() {
                    let const_mont = coeff_to_internal_repr::<F>(col.constant);
                    let const_field = MW::field_new(quote! { #const_mont });
                    let mut col_computation = quote! {
                        let mut col_val = #quartic_struct::from_base(#const_field);
                    };
                    for &(coeff, ref addr) in col.linear_terms.iter() {
                        let idx = addr_to_idx(addr, input_sorted_addrs);
                        let mont = coeff_to_internal_repr::<F>(coeff);
                        let field_coeff = MW::field_new(quote! { #mont });
                        let mul_coeff = MW::mul_assign_by_base(quote! { ct }, field_coeff);
                        let add_ct = MW::add_assign(quote! { col_val }, quote! { ct });
                        col_computation.extend(quote! {
                            let mut ct = unsafe { evals.get_unchecked(#idx) }[j];
                            #mul_coeff;
                            #add_ct;
                        });
                    }
                    // Each column contributes at a different extension field component
                    // For column 0 it's just base, for higher columns multiply by the
                    // corresponding challenge power from the linearization
                    if col_idx == 0 {
                        let add_col = MW::add_assign(quote! { val }, quote! { col_val });
                        val_computation.extend(quote! {
                            {
                                #col_computation
                                #add_col;
                            }
                        });
                    } else {
                        let ci = col_idx - 1;
                        let mul_challenge = MW::mul_assign(
                            quote! { col_val },
                            quote! { lookup_additive_challenge },
                        );
                        let add_col = MW::add_assign(quote! { val }, quote! { col_val });
                        val_computation.extend(quote! {
                            {
                                #col_computation
                                // multiply by challenge^col_idx
                                for _ in 0..#col_idx {
                                    #mul_challenge;
                                }
                                #add_col;
                            }
                        });
                    }
                }
                let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
                let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });
                body.extend(quote! {
                    {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            #val_computation
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                });
            }
            R::LookupPairFromBaseInputs { input, .. } => {
                // Compute 1/(a+γ) + 1/(b+γ) where a, b are inline linear relations
                // num = (a+γ) + (b+γ), den = (a+γ)*(b+γ)
                let gen_linear_relation =
                    |rel: &NoFieldSingleColumnLookupRelation, var_name: &str| {
                        let const_mont = coeff_to_internal_repr::<F>(rel.input.constant);
                        let const_field = MW::field_new(quote! { #const_mont });
                        let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
                        let mut comp = quote! {
                            let mut #var = #quartic_struct::from_base(#const_field);
                        };
                        for &(coeff, ref addr) in rel.input.linear_terms.iter() {
                            let idx = addr_to_idx(addr, input_sorted_addrs);
                            let mont = coeff_to_internal_repr::<F>(coeff);
                            let field_coeff = MW::field_new(quote! { #mont });
                            let tmp = syn::Ident::new(
                                &format!("{}_t", var_name),
                                proc_macro2::Span::call_site(),
                            );
                            let mul_coeff = MW::mul_assign_by_base(quote! { #tmp }, field_coeff);
                            let add_tmp = MW::add_assign(quote! { #var }, quote! { #tmp });
                            comp.extend(quote! {
                                let mut #tmp = unsafe { evals.get_unchecked(#idx) }[j];
                                #mul_coeff;
                                #add_tmp;
                            });
                        }
                        comp
                    };

                let comp_a = gen_linear_relation(&input[0], "a_val");
                let comp_b = gen_linear_relation(&input[1], "b_val");

                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        #comp_a
                        #comp_b
                    },
                    |_, mw_add| {
                        let add_gamma_a =
                            mw_add(quote! { a_val }, quote! { lookup_additive_challenge });
                        let add_gamma_b =
                            mw_add(quote! { b_val }, quote! { lookup_additive_challenge });
                        let add_ab = mw_add(quote! { num }, quote! { b_val });
                        quote! {
                            #add_gamma_a;
                            #add_gamma_b;
                            let mut num = a_val;
                            #add_ab;
                            num
                        }
                    },
                    |mw_mul, _| {
                        let mul_ab = mw_mul(quote! { den }, quote! { b_val });
                        quote! {
                            let mut den = a_val;
                            #mul_ab;
                            den
                        }
                    },
                );
            }
            R::LookupPairFromVectorInputs { input, .. } => {
                // Same as LookupPairFromBaseInputs but with vector (multi-column) inputs
                let gen_vector_relation = |rel: &NoFieldVectorLookupRelation, var_name: &str| {
                    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
                    let mut comp = quote! {
                        let mut #var = #quartic_zero;
                    };
                    for (col_idx, col) in rel.columns.iter().enumerate() {
                        let const_mont = coeff_to_internal_repr::<F>(col.constant);
                        let const_field = MW::field_new(quote! { #const_mont });
                        let col_var = syn::Ident::new(
                            &format!("{}_c{}", var_name, col_idx),
                            proc_macro2::Span::call_site(),
                        );
                        let mut col_comp = quote! {
                            let mut #col_var = #quartic_struct::from_base(#const_field);
                        };
                        for &(coeff, ref addr) in col.linear_terms.iter() {
                            let idx = addr_to_idx(addr, input_sorted_addrs);
                            let mont = coeff_to_internal_repr::<F>(coeff);
                            let field_coeff = MW::field_new(quote! { #mont });
                            let tmp = syn::Ident::new(
                                &format!("{}_c{}_t", var_name, col_idx),
                                proc_macro2::Span::call_site(),
                            );
                            let mul_coeff = MW::mul_assign_by_base(quote! { #tmp }, field_coeff);
                            let add_tmp = MW::add_assign(quote! { #col_var }, quote! { #tmp });
                            col_comp.extend(quote! {
                                let mut #tmp = unsafe { evals.get_unchecked(#idx) }[j];
                                #mul_coeff;
                                #add_tmp;
                            });
                        }
                        let add_col = MW::add_assign(quote! { #var }, quote! { #col_var });
                        if col_idx == 0 {
                            comp.extend(quote! {
                                {
                                    #col_comp
                                    #add_col;
                                }
                            });
                        } else {
                            let mul_challenge = MW::mul_assign(
                                quote! { #col_var },
                                quote! { lookup_additive_challenge },
                            );
                            comp.extend(quote! {
                                {
                                    #col_comp
                                    for _ in 0..#col_idx {
                                        #mul_challenge;
                                    }
                                    #add_col;
                                }
                            });
                        }
                    }
                    comp
                };

                let comp_a = gen_vector_relation(&input[0], "a_val");
                let comp_b = gen_vector_relation(&input[1], "b_val");

                generate_two_output_body::<MW>(
                    &mut body,
                    &mul_batch,
                    quote! {
                        #comp_a
                        #comp_b
                    },
                    |_, mw_add| {
                        let add_gamma_a =
                            mw_add(quote! { a_val }, quote! { lookup_additive_challenge });
                        let add_gamma_b =
                            mw_add(quote! { b_val }, quote! { lookup_additive_challenge });
                        let add_ab = mw_add(quote! { num }, quote! { b_val });
                        quote! {
                            #add_gamma_a;
                            #add_gamma_b;
                            let mut num = a_val;
                            #add_ab;
                            num
                        }
                    },
                    |mw_mul, _| {
                        let mul_ab = mw_mul(quote! { den }, quote! { b_val });
                        quote! {
                            let mut den = a_val;
                            #mul_ab;
                            den
                        }
                    },
                );
            }
            _ => {
                panic!(
                    "Unimplemented relation variant in GKR inlining generator: {:?}",
                    gate.enforced_relation
                );
            }
        }
    }

    body.extend(quote! { acc });

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    quote! {
        #[inline(always)]
        unsafe fn #fn_name(
            evals: &[[#quartic_struct; 2]],
            batch_base: #quartic_struct,
            lookup_additive_challenge: #quartic_struct,
            challenge_powers: &[#quartic_struct; GKR_MAX_POW],
        ) -> [#quartic_struct; 2] {
            #body
        }
    }
}

fn generate_two_output_body<MW: MersenneWrapper>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    setup_vars: TokenStream,
    gen_num: impl FnOnce(
        fn(TokenStream, TokenStream) -> TokenStream,
        fn(TokenStream, TokenStream) -> TokenStream,
    ) -> TokenStream,
    gen_den: impl FnOnce(
        fn(TokenStream, TokenStream) -> TokenStream,
        fn(TokenStream, TokenStream) -> TokenStream,
    ) -> TokenStream,
) {
    let num_expr = gen_num(MW::mul_assign, MW::add_assign);
    let den_expr = gen_den(MW::mul_assign, MW::add_assign);
    let mul_c0 = MW::mul_assign(quote! { c0 }, quote! { out0 });
    let mul_c1 = MW::mul_assign(quote! { c1 }, quote! { out1 });
    let add_c0 = MW::add_assign(quote! { acc[j] }, quote! { c0 });
    let add_c1 = MW::add_assign(quote! { acc[j] }, quote! { c1 });
    body.extend(quote! {
        {
            let bc0 = current_batch;
            #mul_batch;
            let bc1 = current_batch;
            #mul_batch;
            for j in 0..2 {
                #setup_vars
                let out0 = { #num_expr };
                let out1 = { #den_expr };
                let mut c0 = bc0;
                #mul_c0;
                let mut c1 = bc1;
                #mul_c1;
                #add_c0;
                #add_c1;
            }
        }
    });
}
