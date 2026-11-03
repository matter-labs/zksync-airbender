use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;
use prover::cs::gkr_compiler::OutputType;

use super::GKROutputGroupInfo;

pub fn generate_dim_reducing_compute_claim<MW: FieldWrapper>(
    output_groups: &[GKROutputGroupInfo],
) -> TokenStream {
    // Output claims are batched in output order: claim `k` carries `batch_base^k`.
    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    assert!(total_output_polys > 0);
    let last = total_output_polys - 1;
    let claims: Vec<TokenStream> = (0..last)
        .map(|idx| quote! { *output_claims.get_unchecked(#idx) })
        .collect();
    let steps = super::standard_layer::horner_steps::<MW>(quote! { combined }, &claims);

    let quartic_struct = MW::quartic_struct();
    quote! {
        #[inline(always)]
        #[allow(unused_unsafe)]
        unsafe fn dim_reducing_compute_claim(
            output_claims: &[#quartic_struct; #total_output_polys],
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            let mut combined = *output_claims.get_unchecked(#last);
            #steps
            combined
        }
    }
}

pub fn generate_dim_reducing_final_step_accumulator<MW: FieldWrapper>(
    output_groups: &[GKROutputGroupInfo],
) -> TokenStream {
    let quartic_zero = MW::quartic_zero();
    let quartic_struct = MW::quartic_struct();

    // New last-round form: the last output coordinate is already fixed by the univariate
    // sumcheck round, so `evals` is the `[E;2]` line in the remaining pairwise/LSB coordinate.
    // The kernels are evaluated ONCE over that single LSB pair, producing a single batched
    // value `G(point)` (was two values `[G(0), G(1)]` over the last output coordinate).
    let mut blocks = Vec::new();
    let mut idx = 0usize;

    for group in output_groups {
        match group.output_type {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                for _ in 0..group.num_addresses {
                    let mul_v01 = MW::mul_assign(quote! { v01 }, quote! { e1 });
                    let outs = vec![quote! { v01 }];
                    blocks.push((
                        outs,
                        quote! {
                            let si = unsafe { *indices.get_unchecked(#idx) };
                            let es = unsafe { evals.get_unchecked(si) };
                            let e0 = unsafe { *es.get_unchecked(0) };
                            let e1 = unsafe { *es.get_unchecked(1) };
                            let mut v01 = e0;
                            #mul_v01;
                        },
                    ));
                    idx += 1;
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let mul_assign_fn = MW::mul_assign;
                let add_assign_fn = MW::add_assign;

                let mul_num = mul_assign_fn(quote! { num }, quote! { v1b });
                let mul_cb = mul_assign_fn(quote! { cb_tmp }, quote! { v1a });
                let add_num = add_assign_fn(quote! { num }, quote! { cb_tmp });
                let mul_den = mul_assign_fn(quote! { den }, quote! { v1b });
                let outs = vec![quote! { num }, quote! { den }];
                let idx1 = idx + 1;
                blocks.push((
                    outs,
                    quote! {
                        let si0 = unsafe { *indices.get_unchecked(#idx) };
                        let si1 = unsafe { *indices.get_unchecked(#idx1) };
                        let v0 = unsafe { evals.get_unchecked(si0) };
                        let v1 = unsafe { evals.get_unchecked(si1) };
                        let v0a = unsafe { *v0.get_unchecked(0) };
                        let v0b = unsafe { *v0.get_unchecked(1) };
                        let v1a = unsafe { *v1.get_unchecked(0) };
                        let v1b = unsafe { *v1.get_unchecked(1) };
                        // num = v0a * v1b + v0b * v1a
                        let mut num = v0a;
                        #mul_num;
                        let mut cb_tmp = v0b;
                        #mul_cb;
                        #add_num;
                        // den = v1a * v1b
                        let mut den = v1a;
                        #mul_den;
                    },
                ));
                idx += 2;
            }
        }
    }

    let mut body = quote! {
        let mut acc = #quartic_zero;
    };
    for (i, (outs, prefix)) in blocks.into_iter().rev().enumerate() {
        let steps = if i == 0 {
            super::standard_layer::horner_steps_from_zero::<MW>(quote! { acc }, &outs)
        } else {
            super::standard_layer::horner_steps::<MW>(quote! { acc }, &outs)
        };
        body.extend(quote! {
            {
                #prefix
                #steps
            }
        });
    }
    body.extend(quote! { acc });

    quote! {
        #[inline(always)]
        #[allow(unused_unsafe)]
        unsafe fn dim_reducing_final_step_accumulator(
            evals: &[[#quartic_struct; 2]],
            batch_base: #quartic_struct,
            indices: &[usize],
        ) -> #quartic_struct {
            #body
        }
    }
}
