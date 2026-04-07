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
use super::coeff_to_internal_repr;
use super::constraint_kernel::generate_constraint_kernel;

fn coeff64_to_internal_repr<F: PrimeField>(coeff: u64) -> u32 {
    let reduced = (coeff % (F::CHARACTERISTICS as u64)) as u32;
    F::from_u32_with_reduction(reduced).as_u32_raw_repr_reduced()
}

// ---------------------------------------------------------------------------
// Shared code-generation helpers for complex gate types
// ---------------------------------------------------------------------------

/// Generate code that evaluates a `NoFieldLinearRelation` into variable `var_name`.
/// Produces: `let mut {var} = Ext::from_base(const); { term additions... }`
fn emit_linear_relation_eval<MW: MersenneWrapper, F: PrimeField>(
    rel: &prover::cs::definitions::gkr::NoFieldLinearRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let tmp = syn::Ident::new(&format!("{}_t", var_name), proc_macro2::Span::call_site());

    let const_mont = coeff_to_internal_repr::<F>(rel.constant);
    let const_field = MW::field_new(quote! { #const_mont });
    let mut comp = quote! { let mut #var = #quartic_struct::from_base(#const_field); };

    for &(coeff, ref addr) in rel.linear_terms.iter() {
        let idx = addr_to_idx(addr, input_sorted_addrs);
        let mont = coeff_to_internal_repr::<F>(coeff);
        let field_coeff = MW::field_new(quote! { #mont });
        let mul_coeff = MW::mul_assign_by_base(quote! { #tmp }, field_coeff);
        let add_tmp = MW::add_assign(quote! { #var }, quote! { #tmp });
        comp.extend(quote! {
            let mut #tmp = unsafe { evals.get_unchecked(#idx) }[j];
            #mul_coeff;
            #add_tmp;
        });
    }
    comp
}

/// Generate code that evaluates a `NoFieldVectorLookupRelation` via Horner's method
/// into variable `var_name`. Uses `lookup_alpha` as the multiplicative challenge.
fn emit_vector_lookup_eval<MW: MersenneWrapper, F: PrimeField>(
    rel: &NoFieldVectorLookupRelation,
    var_name: &str,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let var = syn::Ident::new(var_name, proc_macro2::Span::call_site());
    let col_var = syn::Ident::new(&format!("{}_cv", var_name), proc_macro2::Span::call_site());
    let tmp = syn::Ident::new(&format!("{}_t", var_name), proc_macro2::Span::call_site());

    let mul_alpha = MW::mul_assign(quote! { #var }, quote! { lookup_alpha });
    let add_col = MW::add_assign(quote! { #var }, quote! { #col_var });

    let mut comp = quote! { let mut #var = #quartic_zero; };

    for col in rel.columns.iter().rev() {
        let const_mont = coeff_to_internal_repr::<F>(col.constant);
        let const_field = MW::field_new(quote! { #const_mont });
        let mut col_comp = quote! { let mut #col_var = #quartic_struct::from_base(#const_field); };

        for &(coeff, ref addr) in col.linear_terms.iter() {
            let idx = addr_to_idx(addr, input_sorted_addrs);
            let mont = coeff_to_internal_repr::<F>(coeff);
            let field_coeff = MW::field_new(quote! { #mont });
            let mul_coeff = MW::mul_assign_by_base(quote! { #tmp }, field_coeff);
            let add_tmp = MW::add_assign(quote! { #col_var }, quote! { #tmp });
            col_comp.extend(quote! {
                let mut #tmp = unsafe { evals.get_unchecked(#idx) }[j];
                #mul_coeff;
                #add_tmp;
            });
        }
        comp.extend(quote! { { #mul_alpha; #col_comp #add_col; } });
    }
    comp
}

/// Emit the standard single-output gate wrapper:
/// `{ let bc = current_batch; advance; for j in 0..2 { val = ...; contrib = bc * val; acc += contrib; } }`
fn emit_single_output_gate<MW: MersenneWrapper>(
    body: &mut TokenStream,
    mul_batch: &TokenStream,
    val_computation: TokenStream,
) {
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

pub fn generate_layer_compute_claim<MW: MersenneWrapper>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    output_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_compute_claim", layer_idx);
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });
    let mul_t = MW::mul_assign(quote! { t }, quote! { claim });
    let add_combined = MW::add_assign(quote! { combined }, quote! { t });
    let mul_t0 = MW::mul_assign(quote! { t0 }, quote! { c0 });
    let mul_t1 = MW::mul_assign(quote! { t1 }, quote! { c1 });
    let add_t0 = MW::add_assign(quote! { combined }, quote! { t0 });
    let add_t1 = MW::add_assign(quote! { combined }, quote! { t1 });

    // Build descriptor array: (num_outputs, idx0, idx1)
    // 0 = no output (constraint), 1 = single, 2 = pair
    let mut descs = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        use NoFieldGKRRelation as R;
        match &gate.enforced_relation {
            R::EnforceConstraintsMaxQuadratic { .. } => {
                descs.push((0usize, 0usize, 0usize));
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
                descs.push((1, addr_to_idx(output, output_sorted_addrs), 0));
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
                descs.push((
                    2,
                    addr_to_idx(&output[0], output_sorted_addrs),
                    addr_to_idx(&output[1], output_sorted_addrs),
                ));
            }
        }
    }

    let num_descs = descs.len();
    let desc_n: Vec<_> = descs.iter().map(|(n, _, _)| *n).collect();
    let desc_o0: Vec<_> = descs.iter().map(|(_, o0, _)| *o0).collect();
    let desc_o1: Vec<_> = descs.iter().map(|(_, _, o1)| *o1).collect();

    quote! {
        #[inline(always)]
        #[allow(clippy::needless_borrow)]
        unsafe fn #fn_name(
            output_claims: &LazyVec<#quartic_struct, GKR_ADDRS>,
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            const DESCS: [(usize, usize, usize); #num_descs] = [
                #( (#desc_n, #desc_o0, #desc_o1), )*
            ];
            let mut combined = #quartic_zero;
            let mut current_batch = #quartic_one;
            let mut i = 0;
            while i < #num_descs {
                let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
                if n == 0 {
                    #mul_batch;
                } else if n == 1 {
                    let claim = output_claims.get(o0);
                    let mut t = current_batch;
                    #mul_t;
                    #add_combined;
                    #mul_batch;
                } else {
                    let c0 = output_claims.get(o0);
                    let mut t0 = current_batch;
                    #mul_t0;
                    #add_t0;
                    #mul_batch;
                    let c1 = output_claims.get(o1);
                    let mut t1 = current_batch;
                    #mul_t1;
                    #add_t1;
                    #mul_batch;
                }
                i += 1;
            }
            combined
        }
    }
}

/// Gate type constants for the dispatch loop in final_step_accumulator.
const GT_COPY: usize = 1;
const GT_PRODUCT: usize = 2; // InitialGrandProductFromCaches, TrivialProduct
const GT_MASK_PRODUCT: usize = 3;
const GT_UNBAL_PRODUCT: usize = 4;
const GT_LOOKUP_PAIR: usize = 5;
const GT_LOOKUP_SETUP: usize = 6;
const GT_LOOKUP_UNBAL: usize = 7;
const GT_AGGREGATE_PAIR: usize = 8;
const GT_LOOKUP_CACHED_DENS: usize = 9;

/// Classify a gate as simple (returns Some(type, indices)) or complex (returns None).
fn classify_gate(
    gate: &prover::cs::gkr_compiler::GateArtifacts,
    input_sorted_addrs: &[GKRAddress],
) -> Option<(usize, [usize; 4])> {
    use NoFieldGKRRelation as R;
    match &gate.enforced_relation {
        R::Copy { input, .. } => Some((GT_COPY, [addr_to_idx(input, input_sorted_addrs), 0, 0, 0])),
        R::InitialGrandProductFromCaches { input, .. } | R::TrivialProduct { input, .. } => Some((
            GT_PRODUCT,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                0,
                0,
            ],
        )),
        R::MaskIntoIdentityProduct { input, mask, .. } => Some((
            GT_MASK_PRODUCT,
            [
                addr_to_idx(input, input_sorted_addrs),
                addr_to_idx(mask, input_sorted_addrs),
                0,
                0,
            ],
        )),
        R::UnbalancedGrandProductWithCache { scalar, input, .. } => Some((
            GT_UNBAL_PRODUCT,
            [
                addr_to_idx(scalar, input_sorted_addrs),
                addr_to_idx(input, input_sorted_addrs),
                0,
                0,
            ],
        )),
        R::LookupPairFromMaterializedBaseInputs { input, .. }
        | R::LookupPairFromMaterializedVectorInputs { input, .. }
        | R::LookupPairFromCachedVectorInputs { input, .. } => Some((
            GT_LOOKUP_PAIR,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                0,
                0,
            ],
        )),
        R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. } => Some((
            GT_LOOKUP_SETUP,
            [
                addr_to_idx(input, input_sorted_addrs),
                addr_to_idx(&setup[0], input_sorted_addrs),
                addr_to_idx(&setup[1], input_sorted_addrs),
                0,
            ],
        )),
        R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => Some((
            GT_LOOKUP_SETUP,
            [
                addr_to_idx(input, input_sorted_addrs),
                addr_to_idx(&setup[0], input_sorted_addrs),
                addr_to_idx(&setup[1], input_sorted_addrs),
                0,
            ],
        )),
        R::LookupUnbalancedPairWithMaterializedBaseInputs {
            input, remainder, ..
        }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs {
            input, remainder, ..
        } => Some((
            GT_LOOKUP_UNBAL,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                addr_to_idx(remainder, input_sorted_addrs),
                0,
            ],
        )),
        R::AggregateLookupRationalPair { input, .. } => Some((
            GT_AGGREGATE_PAIR,
            [
                addr_to_idx(&input[0][0], input_sorted_addrs),
                addr_to_idx(&input[0][1], input_sorted_addrs),
                addr_to_idx(&input[1][0], input_sorted_addrs),
                addr_to_idx(&input[1][1], input_sorted_addrs),
            ],
        )),
        R::LookupWithCachedDensAndSetup { input, setup, .. } => Some((
            GT_LOOKUP_CACHED_DENS,
            [
                addr_to_idx(&input[0], input_sorted_addrs),
                addr_to_idx(&input[1], input_sorted_addrs),
                addr_to_idx(&setup[0], input_sorted_addrs),
                addr_to_idx(&setup[1], input_sorted_addrs),
            ],
        )),
        // Complex gates — stay inline
        _ => None,
    }
}

/// Generate the dispatch loop body for simple gates.
fn generate_simple_gate_loop<MW: MersenneWrapper>(descs: &[(usize, [usize; 4])]) -> TokenStream {
    let field_one = MW::field_one();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    // Single-output gate helpers
    let mul_contrib = MW::mul_assign(quote! { contrib }, quote! { val });
    let add_acc = MW::add_assign(quote! { acc[j] }, quote! { contrib });

    // Pair-output gate helpers
    let mul_c0 = MW::mul_assign(quote! { c0 }, quote! { out0 });
    let mul_c1 = MW::mul_assign(quote! { c1 }, quote! { out1 });
    let add_c0 = MW::add_assign(quote! { acc[j] }, quote! { c0 });
    let add_c1 = MW::add_assign(quote! { acc[j] }, quote! { c1 });

    // Gate-specific ops
    let mul_ab = MW::mul_assign(quote! { val }, quote! { vb });
    let sub_one = MW::sub_assign_base(quote! { val }, field_one.clone());
    let mul_mask = MW::mul_assign(quote! { val }, quote! { mask_val });
    let add_one = MW::add_assign_base(quote! { val }, field_one);
    let mul_si = MW::mul_assign(quote! { val }, quote! { vi });

    // Lookup pair ops
    let add_gamma_bg = MW::add_assign(quote! { bg }, quote! { lookup_additive_challenge });
    let add_gamma_dg = MW::add_assign(quote! { dg }, quote! { lookup_additive_challenge });
    let add_bd = MW::add_assign(quote! { num }, quote! { dg });
    let mul_den = MW::mul_assign(quote! { den }, quote! { dg });

    // Lookup setup ops
    let mul_cb = MW::mul_assign(quote! { cb }, quote! { bg });
    let sub_cb = MW::sub_assign(quote! { num }, quote! { cb });

    // Unbalanced ops
    let add_gamma_r = MW::add_assign(quote! { r_g }, quote! { lookup_additive_challenge });
    let mul_ar = MW::mul_assign(quote! { num }, quote! { r_g });
    let add_b_unbal = MW::add_assign(quote! { num }, quote! { b_val });
    let mul_br = MW::mul_assign(quote! { den }, quote! { r_g });

    // Aggregate pair ops
    let mul_ad = MW::mul_assign(quote! { num }, quote! { d_val });
    let mul_cb_agg = MW::mul_assign(quote! { cb_tmp }, quote! { b_val });
    let add_cb_agg = MW::add_assign(quote! { num }, quote! { cb_tmp });
    let mul_bd_agg = MW::mul_assign(quote! { den }, quote! { d_val });

    // Cached dens ops
    let add_gamma_b_cd = MW::add_assign(quote! { b_cd }, quote! { lookup_additive_challenge });
    let add_gamma_d_cd = MW::add_assign(quote! { d_cd }, quote! { lookup_additive_challenge });
    let mul_ad_cd = MW::mul_assign(quote! { ad_cd }, quote! { d_cd });
    let mul_cb_cd = MW::mul_assign(quote! { cb_cd }, quote! { b_cd });
    let sub_cb_cd = MW::sub_assign(quote! { ad_cd }, quote! { cb_cd });
    let mul_bd_cd = MW::mul_assign(quote! { den }, quote! { d_cd });

    let num_descs = descs.len();
    let desc_gt: Vec<usize> = descs.iter().map(|(gt, _)| *gt).collect();
    let desc_i0: Vec<usize> = descs.iter().map(|(_, idx)| idx[0]).collect();
    let desc_i1: Vec<usize> = descs.iter().map(|(_, idx)| idx[1]).collect();
    let desc_i2: Vec<usize> = descs.iter().map(|(_, idx)| idx[2]).collect();
    let desc_i3: Vec<usize> = descs.iter().map(|(_, idx)| idx[3]).collect();

    quote! {
        {
            const SIMPLE_GATES: [(usize, [usize; 4]); #num_descs] = [
                #( (#desc_gt, [#desc_i0, #desc_i1, #desc_i2, #desc_i3]), )*
            ];
            let mut _sg = 0;
            while _sg < #num_descs {
                let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
                match gt {
                    #GT_COPY => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let val = evals.get_unchecked(idx[0])[j];
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    #GT_PRODUCT => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let vb = evals.get_unchecked(idx[1])[j];
                            #mul_ab;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    #GT_MASK_PRODUCT => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let mask_val = evals.get_unchecked(idx[1])[j];
                            #sub_one;
                            #mul_mask;
                            #add_one;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    #GT_UNBAL_PRODUCT => {
                        let bc = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut val = evals.get_unchecked(idx[0])[j];
                            let vi = evals.get_unchecked(idx[1])[j];
                            #mul_si;
                            let mut contrib = bc;
                            #mul_contrib;
                            #add_acc;
                        }
                    }
                    #GT_LOOKUP_PAIR => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut bg = evals.get_unchecked(idx[0])[j];
                            let mut dg = evals.get_unchecked(idx[1])[j];
                            #add_gamma_bg;
                            #add_gamma_dg;
                            let mut num = bg;
                            #add_bd;
                            let mut den = bg;
                            #mul_den;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    #GT_LOOKUP_SETUP => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let mut bg = evals.get_unchecked(idx[0])[j];
                            let mut dg = evals.get_unchecked(idx[2])[j];
                            let mut cb = evals.get_unchecked(idx[1])[j];
                            #add_gamma_bg;
                            #add_gamma_dg;
                            #mul_cb;
                            let mut num = dg;
                            #sub_cb;
                            let mut den = bg;
                            #mul_den;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    #GT_LOOKUP_UNBAL => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let b_val = evals.get_unchecked(idx[1])[j];
                            let mut r_g = evals.get_unchecked(idx[2])[j];
                            #add_gamma_r;
                            let mut num = a_val;
                            #mul_ar;
                            #add_b_unbal;
                            let mut den = b_val;
                            #mul_br;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    #GT_AGGREGATE_PAIR => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let b_val = evals.get_unchecked(idx[1])[j];
                            let c_val = evals.get_unchecked(idx[2])[j];
                            let d_val = evals.get_unchecked(idx[3])[j];
                            let mut num = a_val;
                            #mul_ad;
                            let mut cb_tmp = c_val;
                            #mul_cb_agg;
                            #add_cb_agg;
                            let mut den = b_val;
                            #mul_bd_agg;
                            let out0 = num;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    #GT_LOOKUP_CACHED_DENS => {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for j in 0..2 {
                            let a_val = evals.get_unchecked(idx[0])[j];
                            let mut b_cd = evals.get_unchecked(idx[1])[j];
                            let c_val = evals.get_unchecked(idx[2])[j];
                            let mut d_cd = evals.get_unchecked(idx[3])[j];
                            #add_gamma_b_cd;
                            #add_gamma_d_cd;
                            let mut ad_cd = a_val;
                            #mul_ad_cd;
                            let mut cb_cd = c_val;
                            #mul_cb_cd;
                            #sub_cb_cd;
                            let mut den = b_cd;
                            #mul_bd_cd;
                            let out0 = ad_cd;
                            let out1 = den;
                            let mut c0 = bc0; #mul_c0; #add_c0;
                            let mut c1 = bc1; #mul_c1; #add_c1;
                        }
                    }
                    _ => unreachable!()
                }
                _sg += 1;
            }
        }
    }
}

pub fn generate_layer_final_step_accumulator<MW: MersenneWrapper, F: PrimeField>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    input_sorted_addrs: &[GKRAddress],
) -> TokenStream {
    let fn_name = quote::format_ident!("layer_{}_final_step_accumulator", layer_idx);
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let quartic_struct = MW::quartic_struct();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let mut body = quote! {
        let mut acc = [#quartic_zero; 2];
        let mut current_batch = #quartic_one;
    };

    // Build segments: alternating inline (complex) and loop (simple) blocks
    let mut simple_group: Vec<(usize, [usize; 4])> = Vec::new();

    let gates: Vec<_> = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .collect();

    for gate in &gates {
        if let Some(desc) = classify_gate(gate, input_sorted_addrs) {
            simple_group.push(desc);
        } else {
            // Flush accumulated simple gates
            if !simple_group.is_empty() {
                body.extend(generate_simple_gate_loop::<MW>(&simple_group));
                simple_group.clear();
            }
            // Emit complex gate inline
            use NoFieldGKRRelation as R;
            match &gate.enforced_relation {
                R::EnforceConstraintsMaxQuadratic { input } => {
                    let kernel_body =
                        generate_constraint_kernel::<MW, F>(input, input_sorted_addrs);
                    let val_comp = quote! { let val = { #kernel_body }; };
                    emit_single_output_gate::<MW>(&mut body, &mul_batch, val_comp);
                }
                R::LinearBaseFieldRelation { input, .. } => {
                    let val_comp =
                        emit_linear_relation_eval::<MW, F>(input, "val", input_sorted_addrs);
                    emit_single_output_gate::<MW>(&mut body, &mul_batch, val_comp);
                }
                R::MaxQuadratic { input, .. } => {
                    let const_mont = coeff64_to_internal_repr::<F>(input.constant);
                    let const_field = MW::field_new(quote! { #const_mont });
                    let mut val_computation = quote! {
                        let mut val = #quartic_struct::from_base(#const_field);
                    };
                    for (addr_a, inner_terms) in input.quadratic_terms.iter() {
                        let ia = addr_to_idx(addr_a, input_sorted_addrs);
                        let mut inner_sum = quote! { let mut inner = #quartic_zero; };
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
                    emit_single_output_gate::<MW>(&mut body, &mul_batch, val_computation);
                }
                R::MaterializeSingleLookupInput { input, .. } => {
                    let val_comp =
                        emit_linear_relation_eval::<MW, F>(&input.input, "val", input_sorted_addrs);
                    emit_single_output_gate::<MW>(&mut body, &mul_batch, val_comp);
                }
                R::MaterializedVectorLookupInput { input, .. } => {
                    let val_comp =
                        emit_vector_lookup_eval::<MW, F>(input, "val", input_sorted_addrs);
                    emit_single_output_gate::<MW>(&mut body, &mul_batch, val_comp);
                }
                R::LookupPairFromBaseInputs { input, .. } => {
                    let comp_a = emit_linear_relation_eval::<MW, F>(
                        &input[0].input,
                        "a_val",
                        input_sorted_addrs,
                    );
                    let comp_b = emit_linear_relation_eval::<MW, F>(
                        &input[1].input,
                        "b_val",
                        input_sorted_addrs,
                    );
                    generate_two_output_body::<MW>(
                        &mut body,
                        &mul_batch,
                        quote! { #comp_a #comp_b },
                        |_, mw_add| {
                            let add_ga =
                                mw_add(quote! { a_val }, quote! { lookup_additive_challenge });
                            let add_gb =
                                mw_add(quote! { b_val }, quote! { lookup_additive_challenge });
                            let add_ab = mw_add(quote! { num }, quote! { b_val });
                            quote! { #add_ga; #add_gb; let mut num = a_val; #add_ab; num }
                        },
                        |mw_mul, _| {
                            let mul_ab = mw_mul(quote! { den }, quote! { b_val });
                            quote! { let mut den = a_val; #mul_ab; den }
                        },
                    );
                }
                R::LookupPairFromVectorInputs { input, .. } => {
                    let comp_a =
                        emit_vector_lookup_eval::<MW, F>(&input[0], "a_val", input_sorted_addrs);
                    let comp_b =
                        emit_vector_lookup_eval::<MW, F>(&input[1], "b_val", input_sorted_addrs);
                    generate_two_output_body::<MW>(
                        &mut body,
                        &mul_batch,
                        quote! { #comp_a #comp_b },
                        |_, mw_add| {
                            let add_ga =
                                mw_add(quote! { a_val }, quote! { lookup_additive_challenge });
                            let add_gb =
                                mw_add(quote! { b_val }, quote! { lookup_additive_challenge });
                            let add_ab = mw_add(quote! { num }, quote! { b_val });
                            quote! { #add_ga; #add_gb; let mut num = a_val; #add_ab; num }
                        },
                        |mw_mul, _| {
                            let mul_ab = mw_mul(quote! { den }, quote! { b_val });
                            quote! { let mut den = a_val; #mul_ab; den }
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
    }

    // Flush remaining simple gates
    if !simple_group.is_empty() {
        body.extend(generate_simple_gate_loop::<MW>(&simple_group));
    }

    body.extend(quote! { acc });

    quote! {
        #[inline(always)]
        #[allow(unused_variables, unused_mut, clippy::needless_borrow, clippy::needless_range_loop, clippy::large_const_arrays)]
        unsafe fn #fn_name(
            evals: &[[#quartic_struct; 2]],
            batch_base: #quartic_struct,
            lookup_additive_challenge: #quartic_struct,
            lookup_alpha: #quartic_struct,
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
