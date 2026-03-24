use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::mersenne_wrapper::MersenneWrapper;
pub use crate::utils::{
    addr_to_idx, collect_extra_addrs_from_cached_relations, collect_sorted_unique_addrs,
    compute_max_pow, transform_gkr_address,
};
use prover::cs::definitions::GKRAddress;
use prover::cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use prover::field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

pub mod constraint_kernel;
pub mod dim_reducing_layer;
pub mod standard_layer;

pub struct GKRGeneratedFiles {
    pub constants: TokenStream,
    pub gkr: TokenStream,
}

#[derive(Clone, Debug)]
pub struct GKROutputGroupInfo {
    pub output_type: OutputType,
    pub num_addresses: usize,
}

pub fn generate_gkr_common<MW: MersenneWrapper>() -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    let sc_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { coeffs[1] });
    let sc_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { coeffs[2] });
    let sc_add_p1_c3 = MW::add_assign(quote! { p1 }, quote! { coeffs[3] });
    let sc_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let sc_mul_sum_eq = MW::mul_assign(quote! { sum }, quote! { eq_prefactor });
    let sc_mul_res_rk = MW::mul_assign(quote! { result }, quote! { r_k });
    let sc_add_res_c2 = MW::add_assign(quote! { result }, quote! { coeffs[2] });
    let sc_add_res_c1 = MW::add_assign(quote! { result }, quote! { coeffs[1] });
    let sc_add_res_c0 = MW::add_assign(quote! { result }, quote! { coeffs[0] });
    let sc_sub_omr_rk = MW::sub_assign(quote! { one_minus_r }, quote! { r_k });
    let sc_sub_omp_p = MW::sub_assign(quote! { one_minus_p }, quote! { p });
    let sc_mul_t_omp = MW::mul_assign(quote! { t }, quote! { one_minus_p });
    let sc_mul_rp_p = MW::mul_assign(quote! { rp }, quote! { p });
    let sc_add_t_rp = MW::add_assign(quote! { t }, quote! { rp });

    let fs_sub_eq0_lpp = MW::sub_assign(quote! { eq0 }, quote! { last_prev_point });
    let fs_mul_rhs_f0 = MW::mul_assign(quote! { rhs }, quote! { f[0] });
    let fs_mul_t_f1 = MW::mul_assign(quote! { t }, quote! { f[1] });
    let fs_add_rhs_t = MW::add_assign(quote! { rhs }, quote! { t });
    let fs_mul_rhs_eq = MW::mul_assign(quote! { rhs }, quote! { final_eq_prefactor });

    let fold_sub_diff_f0 = MW::sub_assign(quote! { diff }, quote! { f0 });
    let fold_mul_diff_lr = MW::mul_assign(quote! { diff }, quote! { last_r });
    let fold_add_diff_f0 = MW::add_assign(quote! { diff }, quote! { f0 });

    let field_from_u32 = MW::field_from_u32_with_reduction(quote! { w });

    quote! {
        #[inline(always)]
        pub fn verify_sumcheck_rounds<
            I: NonDeterminismSource,
            const NUM_ROUNDS: usize,
            const COMMIT_BUF: usize,
        >(
            seed: &mut Seed,
            initial_claim: #quartic_struct,
            challenges: &mut [#quartic_struct],
            layer_idx: usize,
        ) -> Result<(#quartic_struct, #quartic_struct), GKRVerificationError> {
            let mut claim = initial_claim;
            let mut eq_prefactor = #quartic_one;

            let coeff_data_words = 4 * EXT_DEGREE;
            let total_commit_words = BLAKE2S_DIGEST_SIZE_U32_WORDS + coeff_data_words;

            let mut commit_buf: AlignedArray64<u32, COMMIT_BUF> = AlignedArray64::from_value(0u32);
            let mut hasher = DelegatedBlake2sState::new();
            let mut draw_buf = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];

            for round in 0..NUM_ROUNDS {
                commit_buf[0..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&seed.0);

                for i in 0..coeff_data_words {
                    commit_buf[BLAKE2S_DIGEST_SIZE_U32_WORDS + i] = I::read_word();
                }

                let coeffs = unsafe {
                    &*commit_buf
                        .as_ptr()
                        .add(BLAKE2S_DIGEST_SIZE_U32_WORDS)
                        .cast::<[#quartic_struct; 4]>()
                };

                let p0 = coeffs[0];
                let mut p1 = coeffs[0];
                #sc_add_p1_c1;
                #sc_add_p1_c2;
                #sc_add_p1_c3;

                let mut sum = p0;
                #sc_add_sum_p1;
                #sc_mul_sum_eq;

                if sum != claim {
                    return Err(GKRVerificationError::SumcheckRoundFailed {
                        layer: layer_idx,
                        round,
                    });
                }

                Blake2sTranscript::commit_with_seed_using_hasher_and_aligned_buffer(
                    &mut hasher,
                    seed,
                    &commit_buf,
                    total_commit_words,
                );

                Blake2sTranscript::draw_randomness_using_hasher(&mut hasher, seed, &mut draw_buf);
                let r_k = {
                    let mut arr = LazyVec::<#field_struct, EXT_DEGREE>::new();
                    for i in 0..EXT_DEGREE {
                        let w = draw_buf[i];
                        arr.push(#field_from_u32);
                    }
                    unsafe { core::ptr::read(arr.as_slice().as_ptr().cast::<#quartic_struct>()) }
                };

                {
                    let mut result = coeffs[3];
                    #sc_mul_res_rk;
                    #sc_add_res_c2;
                    #sc_mul_res_rk;
                    #sc_add_res_c1;
                    #sc_mul_res_rk;
                    #sc_add_res_c0;
                    claim = result;
                }
                {
                    let p = unsafe { *challenges.get_unchecked(round) };
                    let mut one_minus_r = #quartic_one;
                    #sc_sub_omr_rk;
                    let mut one_minus_p = #quartic_one;
                    #sc_sub_omp_p;
                    let mut t = one_minus_r;
                    #sc_mul_t_omp;
                    let mut rp = r_k;
                    #sc_mul_rp_p;
                    #sc_add_t_rp;
                    eq_prefactor = t;
                }

                unsafe { *challenges.get_unchecked_mut(round) = r_k };
            }

            Ok((claim, eq_prefactor))
        }

        #[inline(always)]
        pub fn verify_final_step_check(
            f: [#quartic_struct; 2],
            last_prev_point: #quartic_struct,
            final_eq_prefactor: #quartic_struct,
            final_claim: #quartic_struct,
            layer_idx: usize,
        ) -> Result<(), GKRVerificationError> {
            let mut eq0 = #quartic_one;
            #fs_sub_eq0_lpp;
            let mut rhs = eq0;
            #fs_mul_rhs_f0;
            let mut t = last_prev_point;
            #fs_mul_t_f1;
            #fs_add_rhs_t;
            #fs_mul_rhs_eq;
            if rhs != final_claim {
                return Err(GKRVerificationError::FinalStepCheckFailed { layer: layer_idx });
            }
            Ok(())
        }

        #[inline(always)]
        pub fn fold_standard_claims<
            const NUM_ADDRS: usize,
            const ADDRS: usize,
            const BUF: usize,
        >(
            eval_buf: &AlignedArray64<MaybeUninit<u32>, BUF>,
            last_r: #quartic_struct,
            claims: &mut LazyVec<#quartic_struct, ADDRS>,
        ) {
            let final_step_evals: &[[#quartic_struct; 2]] =
                unsafe { eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, NUM_ADDRS) };
            claims.clear();
            for i in 0..NUM_ADDRS {
                let evals = unsafe { final_step_evals.get_unchecked(i) };
                let f0 = evals[0];
                let mut diff = evals[1];
                #fold_sub_diff_f0;
                #fold_mul_diff_lr;
                #fold_add_diff_f0;
                claims.push(diff);
            }
        }
    }
}

pub fn generate_gkr_inlined<MW: MersenneWrapper, F: PrimeField, E: FieldExtension<F> + Field, T>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    proof: &GKRProof<F, E, T>,
    final_trace_size_log_2: usize,
    whir_schedule: &WhirSchedule,
) -> GKRGeneratedFiles
where
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    let num_standard_layers = compiled_circuit.layers.len();
    let initial_layer_for_sumcheck = *proof
        .sumcheck_intermediate_values
        .keys()
        .max()
        .expect("proof must have sumcheck values");

    let standard_sorted_addrs: Vec<Vec<GKRAddress>> = compiled_circuit
        .layers
        .iter()
        .map(|l| collect_sorted_unique_addrs(l))
        .collect();

    let build_dim_reducing_addrs = |layer_idx: usize| -> Vec<GKRAddress> {
        let mut addrs = Vec::new();
        if layer_idx == num_standard_layers {
            for (_, group_addrs) in compiled_circuit.global_output_map.iter() {
                for addr in group_addrs.iter() {
                    addrs.push(*addr);
                }
            }
        } else {
            let mut off = 0;
            for (output_type, group_addrs) in compiled_circuit.global_output_map.iter() {
                match output_type {
                    OutputType::PermutationProduct => {
                        for i in 0..group_addrs.len() {
                            addrs.push(GKRAddress::InnerLayer {
                                layer: layer_idx,
                                offset: off + i,
                            });
                        }
                        off += group_addrs.len();
                    }
                    _ => {
                        addrs.push(GKRAddress::InnerLayer {
                            layer: layer_idx,
                            offset: off,
                        });
                        addrs.push(GKRAddress::InnerLayer {
                            layer: layer_idx,
                            offset: off + 1,
                        });
                        off += 2;
                    }
                }
            }
        }
        addrs
    };

    let dim_reducing_sorted_addrs: Vec<Vec<GKRAddress>> = (num_standard_layers
        ..=initial_layer_for_sumcheck)
        .map(|layer_idx| {
            let mut addrs = build_dim_reducing_addrs(layer_idx);
            addrs.sort();
            addrs
        })
        .collect();

    let output_sorted_addrs_per_layer: Vec<Vec<GKRAddress>> = (0..num_standard_layers)
        .map(|layer_idx| {
            use std::collections::BTreeSet;
            let mut addrs: BTreeSet<GKRAddress> = BTreeSet::new();
            if layer_idx + 1 < num_standard_layers {
                for a in &standard_sorted_addrs[layer_idx + 1] {
                    addrs.insert(*a);
                }
                let extras = collect_extra_addrs_from_cached_relations(
                    &compiled_circuit.layers[layer_idx + 1],
                    &standard_sorted_addrs[layer_idx + 1],
                );
                for a in &extras {
                    addrs.insert(*a);
                }
            } else if !dim_reducing_sorted_addrs.is_empty() {
                for a in &dim_reducing_sorted_addrs[0] {
                    addrs.insert(*a);
                }
            } else {
                for a in &standard_sorted_addrs[layer_idx] {
                    addrs.insert(*a);
                }
            }
            addrs.into_iter().collect()
        })
        .collect();

    let get_output_sorted_addrs =
        |layer_idx: usize| -> &[GKRAddress] { &output_sorted_addrs_per_layer[layer_idx] };

    let output_groups: Vec<GKROutputGroupInfo> = compiled_circuit
        .global_output_map
        .iter()
        .map(|(ot, addrs)| GKROutputGroupInfo {
            output_type: *ot,
            num_addresses: addrs.len(),
        })
        .collect();

    let max_sumcheck_rounds = proof
        .sumcheck_intermediate_values
        .values()
        .map(|v| v.sumcheck_num_rounds)
        .max()
        .unwrap_or(0);

    let max_unique_addrs_standard = compiled_circuit
        .layers
        .iter()
        .map(|l| collect_sorted_unique_addrs(l).len())
        .max()
        .unwrap_or(0);

    let max_output_addrs = output_sorted_addrs_per_layer
        .iter()
        .map(|a| a.len())
        .max()
        .unwrap_or(0);
    let max_merged_claims = (0..num_standard_layers)
        .map(|layer_idx| {
            let regular = standard_sorted_addrs[layer_idx].len();
            let extras = collect_extra_addrs_from_cached_relations(
                &compiled_circuit.layers[layer_idx],
                &standard_sorted_addrs[layer_idx],
            )
            .len();
            regular + extras
        })
        .max()
        .unwrap_or(0);
    let max_unique_addrs_standard = max_unique_addrs_standard
        .max(max_output_addrs)
        .max(max_merged_claims);

    let dim_reducing_addr_count: usize = compiled_circuit
        .global_output_map
        .iter()
        .map(|(_, addrs)| addrs.len())
        .sum();
    let max_addrs = max_unique_addrs_standard.max(dim_reducing_addr_count);

    let max_pow = compiled_circuit
        .layers
        .iter()
        .map(|l| compute_max_pow(l))
        .max()
        .unwrap_or(0)
        + 1;

    let total_output_polys: usize = compiled_circuit
        .global_output_map
        .iter()
        .map(|(_, addrs)| addrs.len())
        .sum();
    let max_evals = total_output_polys * (1usize << final_trace_size_log_2);

    let degree = E::DEGREE;
    let digest_words = prover::transcript::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let block_words = prover::transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let dim_reducing_words_per_addr = 4 * degree;
    let standard_words_per_addr = 2 * degree;
    let max_data_words = (max_addrs * dim_reducing_words_per_addr)
        .max(max_addrs * standard_words_per_addr)
        .max(max_evals * degree);
    let total = digest_words + max_data_words;
    let eval_buf_size = (total + block_words - 1) / block_words * block_words;

    let commit_buf_total = digest_words + 4 * degree;
    let commit_buf_size = (commit_buf_total + block_words - 1) / block_words * block_words;

    let initial_transcript_num_u32_words = {
        let mut tmp = Vec::<u32>::new();
        if let Some(top_bits) = proof.inits_and_teardowns_top_bits {
            tmp.push(top_bits);
        }
        proof.external_challenges.flatten_into_buffer(&mut tmp);
        proof
            .whir_proof
            .setup_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        proof
            .whir_proof
            .memory_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        proof
            .whir_proof
            .witness_commitment
            .commitment
            .cap
            .add_into_buffer(&mut tmp);
        tmp.len()
    };

    let mut layer_functions = TokenStream::new();

    for layer_idx in 0..num_standard_layers {
        layer_functions.extend(standard_layer::generate_layer_compute_claim::<MW>(
            &compiled_circuit.layers[layer_idx],
            layer_idx,
            get_output_sorted_addrs(layer_idx),
        ));
        let layer_max_pow = compute_max_pow(&compiled_circuit.layers[layer_idx]) + 1;
        layer_functions.extend(
            standard_layer::generate_layer_final_step_accumulator::<MW, F>(
                &compiled_circuit.layers[layer_idx],
                layer_idx,
                &standard_sorted_addrs[layer_idx],
                layer_max_pow,
            ),
        );
    }

    for (dim_idx, layer_idx) in (num_standard_layers..=initial_layer_for_sumcheck).enumerate() {
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_compute_claim::<MW>(
                &output_groups,
                layer_idx,
            ),
        );
        let iteration_order_addrs = build_dim_reducing_addrs(layer_idx);
        let sorted = &dim_reducing_sorted_addrs[dim_idx];
        let input_sorted_indices: Vec<usize> = iteration_order_addrs
            .iter()
            .map(|addr| addr_to_idx(addr, sorted))
            .collect();
        layer_functions.extend(
            dim_reducing_layer::generate_dim_reducing_final_step_accumulator::<MW>(
                &output_groups,
                &input_sorted_indices,
                layer_idx,
            ),
        );
    }

    let mut static_data = TokenStream::new();

    if !standard_sorted_addrs.is_empty() {
        let sorted = &standard_sorted_addrs[0];
        let mut addrs_stream = TokenStream::new();
        addrs_stream.append_separated(sorted.iter().map(|a| transform_gkr_address(a)), quote! {,});
        static_data.extend(quote! {
            pub const LAYER_0_SORTED_ADDRS: &[GKRAddress] = &[#addrs_stream];
        });
    }

    let base_layer_additional_openings: Vec<TokenStream> = if !compiled_circuit.layers.is_empty() {
        compiled_circuit.layers[0]
            .additional_base_layer_openings
            .iter()
            .map(|a| transform_gkr_address(a))
            .collect()
    } else {
        vec![]
    };
    let mut base_openings_stream = TokenStream::new();
    base_openings_stream.append_separated(base_layer_additional_openings.iter(), quote! {,});

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();

    let mut main_body = TokenStream::new();

    main_body.extend(quote! {
        let mut transcript_buf = LazyVec::<u32, GKR_TRANSCRIPT_U32>::new();
        for _ in 0..GKR_TRANSCRIPT_U32 {
            transcript_buf.push(I::read_word());
        }
        let mut seed = Blake2sTranscript::commit_initial(transcript_buf.as_slice());
        let mut hasher = DelegatedBlake2sState::new();

        let mut init_challenges = [#quartic_zero; 3];
        draw_field_els_into(&mut hasher, &mut seed, &mut init_challenges);
        let lookup_additive_challenge = init_challenges[1];
        let constraints_batch_challenge = init_challenges[2];
    });

    let total_output_polys: usize = output_groups.iter().map(|g| g.num_addresses).sum();
    let evals_per_poly = 1usize << final_trace_size_log_2;
    let total_evals_needed = total_output_polys * evals_per_poly;
    let num_challenges = final_trace_size_log_2 + 1;
    let evaluation_point_len = final_trace_size_log_2;

    let mut claim_accum_body = TokenStream::new();
    let mut eval_offset_val = 0usize;
    for group in &output_groups {
        let count = match group.output_type {
            OutputType::PermutationProduct => group.num_addresses,
            _ => 2,
        };
        for _ in 0..count {
            let off = eval_offset_val;
            let end = eval_offset_val + evals_per_poly;
            claim_accum_body.extend(quote! {
                {
                    let vals: &[#quartic_struct; #evals_per_poly] =
                        evals_slice[#off..#end].try_into().unwrap_unchecked();
                    let eq_arr: &[#quartic_struct; #evals_per_poly] =
                        eq_buf.as_slice().try_into().unwrap_unchecked();
                    let claim = dot_eq(vals, eq_arr);
                    prev_claims.push(claim);
                }
            });
            eval_offset_val += evals_per_poly;
        }
    }

    main_body.extend(quote! {
        let mut evals_flat = [core::mem::MaybeUninit::<#quartic_struct>::uninit(); GKR_EVALS];
        let evals_slice = unsafe {
            let dst = core::slice::from_raw_parts_mut(
                evals_flat.as_mut_ptr().cast::<#quartic_struct>(), #total_evals_needed);
            read_field_els::<I>(dst);
            core::slice::from_raw_parts(evals_flat.as_ptr().cast::<#quartic_struct>(), #total_evals_needed)
        };
        commit_field_els(&mut seed, evals_slice);

        let mut all_challenges = [#quartic_zero; GKR_ROUNDS + 1];
        draw_field_els_into(
            &mut hasher, &mut seed, &mut all_challenges[..#num_challenges]);
        let batching_challenge = all_challenges[#num_challenges - 1];

        let mut eq_buf = LazyVec::<#quartic_struct, #evals_per_poly>::new();
        let eq_challenges: &[#quartic_struct; #evaluation_point_len] =
            all_challenges[..#evaluation_point_len].try_into().unwrap_unchecked();
        make_eq_poly(eq_challenges, &mut eq_buf);

        let mut prev_claims: LazyVec<#quartic_struct, GKR_ADDRS> = LazyVec::new();
        #claim_accum_body

        let mut prev_point = [#quartic_zero; GKR_ROUNDS];
        prev_point[..#evaluation_point_len].copy_from_slice(&all_challenges[..#evaluation_point_len]);

        let mut state = LayerState {
            prev_point,
            prev_point_len: #evaluation_point_len,
            prev_claims,
            batching_challenge,
        };

        let mut eval_buf = AlignedArray64::<u32, GKR_EVAL_BUF>::new_uninit();
    });

    for config_idx in (num_standard_layers..=initial_layer_for_sumcheck).rev() {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("missing sumcheck values");
        let num_sumcheck_rounds = proof_values.sumcheck_num_rounds;
        let dim_idx = config_idx - num_standard_layers;
        let num_input_addrs = dim_reducing_sorted_addrs[dim_idx].len();
        let compute_claim_fn = quote::format_ident!("dim_reducing_{}_compute_claim", config_idx);
        let final_step_fn =
            quote::format_ident!("dim_reducing_{}_final_step_accumulator", config_idx);
        let num_regular_rounds = num_sumcheck_rounds - 1;

        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(&state.prev_claims, state.batching_challenge);
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut seed, initial_claim, &mut state.prev_point, #config_idx)?;
                let mut fc_len = #num_regular_rounds;
                let data_words = #num_input_addrs * 4 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
                {
                    let evals: &[[#quartic_struct; 4]] = eval_buf.transmute_subslice(
                        BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_input_addrs);
                    let f = #final_step_fn(evals, state.batching_challenge);
                    verify_final_step_check(f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
                let mut draw_buf = [#quartic_zero; 3];
                draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
                let r_before_last = draw_buf[0];
                let r_last = draw_buf[1];
                let next_batching = draw_buf[2];
                *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
                fc_len += 1;
                *state.prev_point.get_unchecked_mut(fc_len) = r_last;
                fc_len += 1;
                const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
                const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
                let mut eq4 = LazyVec::<#quartic_struct, DIM_REDUCING_EQ_SIZE>::new();
                make_eq_poly(&[r_before_last, r_last], &mut eq4);
                let evals: &[[#quartic_struct; DIM_REDUCING_EQ_SIZE]] = eval_buf.transmute_subslice(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_input_addrs);
                let eq4_arr: &[#quartic_struct; DIM_REDUCING_EQ_SIZE] =
                    eq4.as_slice().try_into().unwrap_unchecked();
                state.prev_claims.clear();
                for i in 0..#num_input_addrs {
                    let e = evals.get_unchecked(i);
                    state.prev_claims.push(dot_eq(e, eq4_arr));
                }
                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
            }
        });
    }

    if num_standard_layers > 0 {
        let mul_cb = MW::mul_assign(quote! { pow }, quote! { constraints_batch_challenge });
        main_body.extend(quote! {
            let challenge_powers: [#quartic_struct; GKR_MAX_POW] = {
                let mut lv = LazyVec::<#quartic_struct, GKR_MAX_POW>::new();
                let mut pow = #quartic_one;
                for _ in 0..GKR_MAX_POW {
                    lv.push(pow);
                    #mul_cb;
                }
                unsafe { lv.into_array() }
            };
        });
    }

    for config_idx in (0..num_standard_layers).rev() {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("missing sumcheck values");
        let num_sumcheck_rounds = proof_values.sumcheck_num_rounds;
        let num_dedup_addrs = standard_sorted_addrs[config_idx].len();
        let compute_claim_fn = quote::format_ident!("layer_{}_compute_claim", config_idx);
        let final_step_fn = quote::format_ident!("layer_{}_final_step_accumulator", config_idx);
        let num_regular_rounds = num_sumcheck_rounds - 1;

        let extra_addrs = collect_extra_addrs_from_cached_relations(
            &compiled_circuit.layers[config_idx],
            &standard_sorted_addrs[config_idx],
        );
        let num_extra = extra_addrs.len();

        let fold_and_extras_code = if num_extra > 0 {
            let regular_set: std::collections::BTreeSet<GKRAddress> =
                standard_sorted_addrs[config_idx].iter().copied().collect();
            let mut target_addrs: std::collections::BTreeSet<GKRAddress> = regular_set.clone();
            for a in &extra_addrs {
                target_addrs.insert(*a);
            }
            let target_addrs: Vec<GKRAddress> = target_addrs.into_iter().collect();

            let sub = MW::sub_assign(quote! { diff }, quote! { f0 });
            let mul_r = MW::mul_assign(quote! { diff }, quote! { last_r });
            let add_f0 = MW::add_assign(quote! { diff }, quote! { f0 });
            let mut build_stmts = TokenStream::new();
            build_stmts.extend(quote! {
                let mut extra_evals = [#quartic_zero; #num_extra];
                read_field_els::<I>(&mut extra_evals);
                commit_field_els(&mut seed, &extra_evals);
                let final_step_evals: &[[#quartic_struct; 2]] = eval_buf.transmute_subslice(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_dedup_addrs);
                state.prev_claims.clear();
            });

            let mut regular_idx = 0usize;
            let mut extra_idx = 0usize;
            for addr in target_addrs.iter() {
                if regular_set.contains(addr) {
                    build_stmts.extend(quote! {
                        {
                            let ev = unsafe { final_step_evals.get_unchecked(#regular_idx) };
                            let f0 = ev[0];
                            let mut diff = ev[1];
                            #sub; #mul_r; #add_f0;
                            state.prev_claims.push(diff);
                        }
                    });
                    regular_idx += 1;
                } else {
                    build_stmts.extend(quote! {
                        state.prev_claims.push(extra_evals[#extra_idx]);
                    });
                    extra_idx += 1;
                }
            }
            build_stmts
        } else {
            quote! {
                fold_standard_claims::<#num_dedup_addrs, GKR_ADDRS, GKR_EVAL_BUF>(
                    &eval_buf, last_r, &mut state.prev_claims);
            }
        };

        main_body.extend(quote! {
            {
                let initial_claim = #compute_claim_fn(&state.prev_claims, state.batching_challenge);
                let (final_claim, final_eq_prefactor) =
                    verify_sumcheck_rounds::<I, #num_regular_rounds, GKR_COMMIT_BUF>(
                        &mut seed, initial_claim, &mut state.prev_point, #config_idx)?;
                let mut fc_len = #num_regular_rounds;
                let data_words = #num_dedup_addrs * 2 * <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
                {
                    let evals: &[[#quartic_struct; 2]] = eval_buf.transmute_subslice(
                        BLAKE2S_DIGEST_SIZE_U32_WORDS, #num_dedup_addrs);
                    let f = #final_step_fn(evals, state.batching_challenge,
                        lookup_additive_challenge, &challenge_powers);
                    verify_final_step_check(f,
                        *state.prev_point.get_unchecked(state.prev_point_len - 1),
                        final_eq_prefactor, final_claim, #config_idx)?;
                }
                commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
                let mut draw_buf = [#quartic_zero; 2];
                draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
                let last_r = draw_buf[0];
                let next_batching = draw_buf[1];
                *state.prev_point.get_unchecked_mut(fc_len) = last_r;
                fc_len += 1;
                #fold_and_extras_code
                state.batching_challenge = next_batching;
                state.prev_point_len = fc_len;
            }
        });
    }

    main_body.extend(quote! {
        let grand_product_accumulator: #quartic_struct = read_field_el::<I>();
        commit_field_els(&mut seed, &[grand_product_accumulator]);
        let mut draw_buf = [#quartic_zero; 1];
        draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
        let whir_batching_challenge = draw_buf[0];
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            grand_product_accumulator,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge,
            whir_transcript_seed: seed,
        })
    });

    let field_use_stmts = MW::field_use_statements();

    let trace_len_log2 = proof
        .sumcheck_intermediate_values
        .get(&0)
        .expect("proof must have sumcheck values for layer 0")
        .sumcheck_num_rounds;

    let whir_rounds = whir_schedule.whir_steps_schedule.len();
    let whir_fold_steps = &whir_schedule.whir_steps_schedule;
    let whir_queries = &whir_schedule.whir_queries_schedule;
    let whir_pow_bits = &whir_schedule.whir_pow_schedule;
    let whir_lde_factors = &whir_schedule.whir_steps_lde_factors;
    let whir_base_lde_factor = whir_schedule.base_lde_factor;
    let whir_cap_size = whir_schedule.cap_size;
    let whir_cap_size_log2 = whir_cap_size.trailing_zeros() as usize;

    let total_fold_steps: usize = whir_fold_steps.iter().sum();
    assert!(
        trace_len_log2 >= total_fold_steps,
        "total fold steps ({}) exceed trace_len_log2 ({})",
        total_fold_steps,
        trace_len_log2
    );
    let final_m = trace_len_log2 - total_fold_steps;
    let final_monomials_len = 1usize << final_m;

    let (num_memory_claims, num_witness_claims, num_setup_claims) =
        if !standard_sorted_addrs.is_empty() {
            let mut mem = 0usize;
            let mut wit = 0usize;
            let mut setup = 0usize;
            for addr in &standard_sorted_addrs[0] {
                match addr {
                    GKRAddress::BaseLayerMemory(_) => mem += 1,
                    GKRAddress::BaseLayerWitness(_) => wit += 1,
                    GKRAddress::Setup(_) => setup += 1,
                    _ => {}
                }
            }
            (mem, wit, setup)
        } else {
            (0, 0, 0)
        };
    let num_base_claims = num_memory_claims + num_witness_claims + num_setup_claims;

    let base_lde_factor_log2 = whir_base_lde_factor.trailing_zeros() as usize;
    let initial_fold_steps = whir_fold_steps[0];
    let base_oracle_depth =
        trace_len_log2 + base_lde_factor_log2 - initial_fold_steps - whir_cap_size_log2;

    let num_intermediate_oracles = whir_rounds - 1;
    let mut whir_oracle_depths = Vec::with_capacity(num_intermediate_oracles);
    {
        let mut poly_size_log2 = trace_len_log2;
        for i in 0..num_intermediate_oracles {
            poly_size_log2 -= whir_fold_steps[i];
            let lde_factor_log2 = whir_lde_factors[i].trailing_zeros() as usize;
            let next_fold_steps = whir_fold_steps[i + 1];
            let depth = poly_size_log2 + lde_factor_log2 - next_fold_steps - whir_cap_size_log2;
            whir_oracle_depths.push(depth);
        }
    }

    let constants = quote! {
        use ::verifier_common::cs::definitions::GKRAddress;
        pub const GKR_ROUNDS: usize = #max_sumcheck_rounds;
        pub const GKR_ADDRS: usize = #max_addrs;
        pub const GKR_EVALS: usize = #max_evals;
        pub const GKR_TRANSCRIPT_U32: usize = #initial_transcript_num_u32_words;
        pub const GKR_MAX_POW: usize = #max_pow;
        pub const GKR_EVAL_BUF: usize = #eval_buf_size;
        pub const GKR_COMMIT_BUF: usize = #commit_buf_size;
        #static_data
        pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[#base_openings_stream];
        pub const WHIR_ROUNDS: usize = #whir_rounds;
        pub const WHIR_FOLD_STEPS: [usize; #whir_rounds] = [#(#whir_fold_steps),*];
        pub const WHIR_QUERIES: [usize; #whir_rounds] = [#(#whir_queries),*];
        pub const WHIR_POW_BITS: [u32; #whir_rounds] = [#(#whir_pow_bits),*];
        pub const WHIR_BASE_LDE_FACTOR: usize = #whir_base_lde_factor;
        pub const WHIR_LDE_FACTORS: [usize; #num_intermediate_oracles] = [#(#whir_lde_factors),*];
        pub const WHIR_CAP_SIZE: usize = #whir_cap_size;
        pub const FINAL_M: usize = #final_m;
        pub const FINAL_MONOMIALS_LEN: usize = #final_monomials_len;
        pub const NUM_BASE_CLAIMS: usize = #num_base_claims;
        pub const NUM_MEMORY_CLAIMS: usize = #num_memory_claims;
        pub const NUM_WITNESS_CLAIMS: usize = #num_witness_claims;
        pub const NUM_SETUP_CLAIMS: usize = #num_setup_claims;
        pub const BASE_ORACLE_DEPTH: usize = #base_oracle_depth;
        pub const WHIR_ORACLE_DEPTHS: [usize; #num_intermediate_oracles] = [#(#whir_oracle_depths),*];
    };

    let gkr = quote! {
        #field_use_stmts
        use ::verifier_common::cs::definitions::GKRAddress;
        use ::verifier_common::gkr::{
            GKRVerifierOutput, GKRVerificationError, LayerState, LazyVec,
            read_eval_data_from_nds, commit_eval_buffer,
        };
        use super::common::{
            verify_sumcheck_rounds, verify_final_step_check, fold_standard_claims,
            make_eq_poly, dot_eq, draw_field_els_into, read_field_el, read_field_els, commit_field_els,
        };
        use ::verifier_common::field_ops;
        use ::verifier_common::transcript::{Blake2sTranscript, Seed};
        use ::verifier_common::blake2s_u32::{AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use super::constants::*;

        #layer_functions

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
        pub fn verify_gkr_sumcheck<I: NonDeterminismSource,
        >() -> Result<GKRVerifierOutput<'static, #quartic_struct, GKR_ROUNDS, GKR_ADDRS>, GKRVerificationError> {
            unsafe { #main_body }
        }
    };

    GKRGeneratedFiles { constants, gkr }
}
