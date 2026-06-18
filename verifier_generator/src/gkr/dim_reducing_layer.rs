use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;
use prover::cs::gkr_compiler::OutputType;

use super::GKROutputGroupInfo;

pub fn generate_dim_reducing_compute_claim<MW: FieldWrapper>(
    output_groups: &[GKROutputGroupInfo],
) -> TokenStream {
    let quartic_one = MW::quartic_one();

    let mut body = quote! {
        let mut current_batch = #quartic_one;
    };

    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });
    let mut out_idx = 0usize;
    let mut first_contributing = true;

    for group in output_groups {
        match group.output_type {
            OutputType::PermutationProduct => {
                for _ in 0..group.num_addresses {
                    let idx = out_idx;
                    out_idx += 1;
                    let mul_t = MW::mul_assign(quote! { t }, quote! { claim });
                    if first_contributing {
                        first_contributing = false;
                        body.extend(quote! {
                            let combined = {
                                let bc = current_batch;
                                #mul_batch;
                                let claim = *output_claims.get_unchecked(#idx);
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
                                #mul_batch;
                                let claim = *output_claims.get_unchecked(#idx);
                                let mut t = bc;
                                #mul_t;
                                #add_combined;
                            }
                        });
                    }
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                assert!(
                    !first_contributing,
                    "lookup group cannot be first contributing gate"
                );
                let idx0 = out_idx;
                let idx1 = out_idx + 1;
                out_idx += 2;
                let mul_t = MW::mul_assign(quote! { t }, quote! { claim });
                let add_combined = MW::add_assign(quote! { combined }, quote! { t });
                body.extend(quote! {
                    {
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        for (bc, idx) in [(bc0, #idx0), (bc1, #idx1)] {
                            let claim = *output_claims.get_unchecked(idx);
                            let mut t = bc;
                            #mul_t;
                            #add_combined;
                        }
                    }
                });
            }
        }
    }

    body.extend(quote! { combined });

    let quartic_struct = MW::quartic_struct();
    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    quote! {
        #[inline(always)]
        #[allow(unused_unsafe)]
        unsafe fn dim_reducing_compute_claim(
            output_claims: &[#quartic_struct; #total_output_polys],
            batch_base: #quartic_struct,
        ) -> #quartic_struct {
            #body
        }
    }
}

pub fn generate_dim_reducing_final_step_accumulator<MW: FieldWrapper>(
    output_groups: &[GKROutputGroupInfo],
) -> TokenStream {
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let quartic_struct = MW::quartic_struct();
    let mul_batch = MW::mul_assign(quote! { current_batch }, quote! { batch_base });

    let mut body = quote! {
        let mut acc = [#quartic_zero; 2];
        let mut current_batch = #quartic_one;
        let mut _idx = 0usize;
    };

    for group in output_groups {
        match group.output_type {
            OutputType::PermutationProduct => {
                for _ in 0..group.num_addresses {
                    let mul_v01 = MW::mul_assign(quote! { v01 }, quote! { e1 });
                    let mul_c0 = MW::mul_assign(quote! { c0 }, quote! { v01 });
                    let add_a0 = MW::add_assign(quote! { acc[0] }, quote! { c0 });
                    let mul_v23 = MW::mul_assign(quote! { v23 }, quote! { e3 });
                    let mul_c1 = MW::mul_assign(quote! { c1 }, quote! { v23 });
                    let add_a1 = MW::add_assign(quote! { acc[1] }, quote! { c1 });
                    body.extend(quote! {
                        {
                            let si = unsafe { *indices.get_unchecked(_idx) };
                            _idx += 1;
                            let bc = current_batch;
                            #mul_batch;
                            let es = unsafe { evals.get_unchecked(si) };
                            let e0 = unsafe { *es.get_unchecked(0) };
                            let e1 = unsafe { *es.get_unchecked(1) };
                            let e2 = unsafe { *es.get_unchecked(2) };
                            let e3 = unsafe { *es.get_unchecked(3) };
                            let mut v01 = e0;
                            #mul_v01;
                            let mut c0 = bc;
                            #mul_c0;
                            #add_a0;
                            let mut v23 = e2;
                            #mul_v23;
                            let mut c1 = bc;
                            #mul_c1;
                            #add_a1;
                        }
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let mul_assign_fn = MW::mul_assign;
                let add_assign_fn = MW::add_assign;

                let mut lookup_body = TokenStream::new();
                for (a0, a1, b0, b1, acc_idx) in [
                    (0usize, 1usize, 0usize, 1usize, 0usize),
                    (2usize, 3usize, 2usize, 3usize, 1usize),
                ]
                .iter()
                {
                    let mul_num = mul_assign_fn(quote! { num }, quote! { v1b });
                    let mul_cb = mul_assign_fn(quote! { cb_tmp }, quote! { v1a });
                    let add_num = add_assign_fn(quote! { num }, quote! { cb_tmp });
                    let mul_den = mul_assign_fn(quote! { den }, quote! { v1b });
                    let mul_c0 = mul_assign_fn(quote! { c0_tmp }, quote! { num });
                    let mul_c1 = mul_assign_fn(quote! { c1_tmp }, quote! { den });
                    let add_a0 = add_assign_fn(quote! { acc[#acc_idx] }, quote! { c0_tmp });
                    let add_a1 = add_assign_fn(quote! { acc[#acc_idx] }, quote! { c1_tmp });
                    lookup_body.extend(quote! {
                        {
                            let v0a = unsafe { *v0.get_unchecked(#a0) };
                            let v0b = unsafe { *v0.get_unchecked(#a1) };
                            let v1a = unsafe { *v1.get_unchecked(#b0) };
                            let v1b = unsafe { *v1.get_unchecked(#b1) };
                            // num = v0a * v1b + v0b * v1a
                            let mut num = v0a;
                            #mul_num;
                            let mut cb_tmp = v0b;
                            #mul_cb;
                            #add_num;
                            // den = v1a * v1b
                            let mut den = v1a;
                            #mul_den;
                            let mut c0_tmp = bc0;
                            #mul_c0;
                            let mut c1_tmp = bc1;
                            #mul_c1;
                            #add_a0;
                            #add_a1;
                        }
                    });
                }

                body.extend(quote! {
                    {
                        let si0 = unsafe { *indices.get_unchecked(_idx) };
                        let si1 = unsafe { *indices.get_unchecked(_idx + 1) };
                        _idx += 2;
                        let bc0 = current_batch;
                        #mul_batch;
                        let bc1 = current_batch;
                        #mul_batch;
                        let v0 = unsafe { evals.get_unchecked(si0) };
                        let v1 = unsafe { evals.get_unchecked(si1) };
                        #lookup_body
                    }
                });
            }
        }
    }

    body.extend(quote! { acc });

    quote! {
        #[inline(always)]
        #[allow(unused_unsafe)]
        unsafe fn dim_reducing_final_step_accumulator(
            evals: &[[#quartic_struct; 4]],
            batch_base: #quartic_struct,
            indices: &[usize],
        ) -> [#quartic_struct; 2] {
            #body
        }
    }
}
