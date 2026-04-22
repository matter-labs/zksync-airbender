use std::collections::BTreeMap;

use proc_macro2::TokenStream;
use quote::quote;

use crate::gkr::{OracleInfo, OracleType};
use crate::mersenne_wrapper::MersenneWrapper;
use prover::gkr::prover::WhirSchedule;

/// Compute draw_words for a given number of queries and query index bits.
fn compute_draw_words(num_queries: usize, query_index_bits: usize) -> usize {
    let total_bits = num_queries * query_index_bits + 32;
    total_bits.div_ceil(256) * prover::transcript::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS
}

/// Parameters for a single WHIR round, derived from the schedule.
struct RoundParams {
    fold_steps: usize,
    values_per_leaf: usize,
    num_queries: usize,
    pow_bits: u32,
    query_index_bits: usize,
    rs_domain_log2: usize,
    num_cosets: usize,
    num_cosets_log2: usize,
    coset_tree_size: usize,
    draw_words: usize,
}

/// Compute round parameters from schedule and poly_size_log2.
fn round_params(
    whir_schedule: &WhirSchedule,
    round_idx: usize,
    poly_size_log2: usize,
    lde_factor: usize,
) -> RoundParams {
    let fold_steps = whir_schedule.whir_steps_schedule[round_idx];
    let values_per_leaf = 1usize << fold_steps;
    let lde_factor_log2 = lde_factor.trailing_zeros() as usize;
    let rs_domain_log2 = poly_size_log2 + lde_factor_log2;
    let query_index_bits = rs_domain_log2 - fold_steps;
    let num_queries = whir_schedule.whir_queries_schedule[round_idx];
    let coset_tree_size = (1usize << poly_size_log2) / values_per_leaf;
    RoundParams {
        fold_steps,
        values_per_leaf,
        num_queries,
        pow_bits: whir_schedule.whir_pow_schedule[round_idx],
        query_index_bits,
        rs_domain_log2,
        num_cosets: lde_factor,
        num_cosets_log2: lde_factor_log2,
        coset_tree_size,
        draw_words: compute_draw_words(num_queries, query_index_bits),
    }
}

/// Generate the query loop body for reading a single-oracle leaf, hashing, verifying
/// merkle path, extracting evals, and folding. Used by both internal and final rounds.
fn generate_single_oracle_query_body<MW: MersenneWrapper>(
    leaf_ext_words_expr: TokenStream,
    hash_buf_size_const: TokenStream,
    values_per_leaf_expr: TokenStream,
    fold_steps_expr: TokenStream,
    oracle_depth_expr: TokenStream,
    oracle_cap_expr: TokenStream,
) -> TokenStream {
    let quartic_struct = MW::quartic_struct();

    quote! {
        {
            let mut i = 0;
            while i < #leaf_ext_words_expr {
                hash_buf.write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        let block_end = (#leaf_ext_words_expr).next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
        hash_buf.zero_range(#leaf_ext_words_expr, block_end);

        let init_buf = hash_buf.assume_init_subarray::<#hash_buf_size_const>();
        hash_leaf_data_into_state(&mut ts.hasher, init_buf, #leaf_ext_words_expr);
        if !verify_merkle_path::<I>(
            &mut ts.hasher, tree_index, #oracle_depth_expr, #oracle_cap_expr,
        ) {
            return Err(E::whir_merkle_path_failed(q));
        }

        let mut evals: LazyVec<#quartic_struct, { #values_per_leaf_expr }> =
            LazyVec::new();
        let mut j = 0;
        while j < #values_per_leaf_expr {
            evals.push(ext_from_raw_word_slice(
                &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
            ));
            j += 1;
        }

        let folded = fold_coset(
            evals.as_slice(), #fold_steps_expr,
            folding_challenges.as_slice(),
            base_root_inv, high_powers_offsets.as_slice(),
            fold_buf_a.as_mut_slice(), fold_buf_b.as_mut_slice(),
        );
    }
}

// ---- Initial Round ----

pub fn generate_whir_initial_round<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    oracles: &BTreeMap<OracleType, OracleInfo>,
    trace_len_log2: usize,
) -> TokenStream {
    let field_use_stmts = MW::field_use_statements();
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();

    let params = round_params(
        whir_schedule,
        0,
        trace_len_log2,
        whir_schedule.base_lde_factor,
    );

    let oracle_leaf_words: Vec<usize> = oracles
        .iter()
        .map(|(_, o)| o.num_columns * params.values_per_leaf)
        .collect();
    let max_leaf_words = oracle_leaf_words.iter().copied().max().unwrap_or(0);
    let block_words = prover::transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let hash_buf_padded = max_leaf_words.div_ceil(block_words) * block_words;

    let values_per_leaf = params.values_per_leaf;
    let query_index_bits = params.query_index_bits;
    let initial_num_queries = params.num_queries;
    let initial_pow_bits = params.pow_bits;
    let draw_words = params.draw_words;
    let rs_domain_log2 = params.rs_domain_log2;
    let num_cosets = params.num_cosets;
    let num_cosets_log2 = params.num_cosets_log2;
    let coset_tree_size = params.coset_tree_size;
    let fold_buf_half = values_per_leaf / 2;

    let mul_delin = MW::mul_assign(quote! { t }, quote! { current_delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );
    let advance_current_delin = MW::mul_assign(
        quote! { current_delinearization_challenge },
        quote! { delinearization_challenge },
    );
    let batch_mul_eval = MW::mul_assign(quote! { term }, quote! { eval });
    let add_claim_eval = MW::add_assign(quote! { claim }, quote! { term });

    // Build unrolled per-oracle query calls with const-generic LEAF_WORDS
    let mut unrolled_oracle_queries = TokenStream::new();
    {
        let mut gamma_offset_acc = 0usize;
        for (oracle_type, oracle_info) in oracles.iter() {
            let num_cols = oracle_info.num_columns;
            let leaf_words = num_cols * params.values_per_leaf;
            let gamma_off = gamma_offset_acc;
            let depth = oracle_info.depth;

            if num_cols > 0 {
                unrolled_oracle_queries.extend(quote! {
                    process_oracle_query::<I, E, WHIR_HASH_BUF_SIZE, #leaf_words>(
                        &mut ts.hasher, hash_buf,
                        #num_cols, tree_index,
                        #depth,
                        initial_transcript. #oracle_type (),
                        &gamma_powers[..], #gamma_off,
                        &mut acc0, &mut acc1, q,
                    )?;
                });
            }
            gamma_offset_acc += num_cols;
        }
    }

    quote! {
        #field_use_stmts
        use core::mem::MaybeUninit;
        use ::verifier_common::field::{Field, FieldExtension};
        use ::verifier_common::field_ops;
        use ::verifier_common::blake2s_u32::{
            AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS,
            BLAKE2S_DIGEST_SIZE_U32_WORDS,
        };
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::lazy_vec::LazyVec;
        use ::verifier_common::whir::{
            read_commit_return_merkle_cap,
            read_and_verify_pow,
            draw_query_indices,
        };
        use super::common::{
            verify_whir_sumcheck_step, fold_coset, materialize_gamma_powers,
            read_field_el, read_field_els,
            read_reduced_field_el, draw_single_field_el, compute_tree_index,
            process_oracle_query,
            fold_whir_accumulator, push_whir_pow_entry,
        };
        use ::verifier_common::errors::ErrorCreator;
        use ::verifier_common::structs::{CommitBuf, TranscriptState};
        use super::constants::*;

        const INITIAL_VALUES_PER_LEAF: usize = #values_per_leaf;
        const INITIAL_QUERY_INDEX_BITS: usize = #query_index_bits;
        const INITIAL_NUM_QUERIES: usize = #initial_num_queries;
        const INITIAL_POW_BITS: u32 = #initial_pow_bits;
        const INITIAL_DRAW_WORDS: usize = #draw_words;
        const INITIAL_RS_DOMAIN_LOG2: usize = #rs_domain_log2;
        const HASH_BUF_SIZE: usize = #hash_buf_padded;
        const FOLD_BUF_HALF: usize = #fold_buf_half;
        const NUM_COSETS: usize = #num_cosets;
        const NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const COSET_TREE_SIZE: usize = #coset_tree_size;

        pub fn verify_initial_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
            initial_transcript: &ConcreteInitialTranscript,
            ts: &mut TranscriptState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            batching_challenge: #quartic_struct,
            base_layer_claims: &[#quartic_struct],
            z_initial: &[#quartic_struct],
            accumulator: &mut ::verifier_common::whir::WhirAccumulator<
                #quartic_struct, MAX_POW_ENTRIES,
            >,
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), E::Error> {
            unsafe {
                let gamma_powers: [#quartic_struct; TOTAL_ORACLE_COLS] =
                    materialize_gamma_powers(batching_challenge);
                let mut claim = #quartic_zero;
                {
                    let mut col_idx = 0;
                    while col_idx < TOTAL_ORACLE_COLS {
                        let claim_idx = *INITIAL_WHIR_CLAIM_INDICES.get_unchecked(col_idx);
                        let eval: #quartic_struct = *base_layer_claims.get_unchecked(claim_idx);
                        let mut term = *gamma_powers.get_unchecked(col_idx);
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                    }
                }

                let mut folding_challenges: LazyVec<#quartic_struct, { WHIR_FOLD_STEPS[0] }> =
                    LazyVec::new();
                let mut round_idx = 0;
                while round_idx < WHIR_FOLD_STEPS[0] {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(
                        ts, claim, round_idx,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    fold_whir_accumulator(accumulator, alpha, z_initial);
                    round_idx += 1;
                }

                const CAP_COMMIT_BUF: usize = {
                    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_CAP_WORDS;
                    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let intermediate_cap =
                    read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(ts);

                let ood_point = draw_single_field_el(ts);

                const OOD_DATA_WORDS: usize = super::common::EXT_DEGREE;
                const OOD_COMMIT_BUF: usize = {
                    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + OOD_DATA_WORDS;
                    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let mut ood_buf = CommitBuf::<OOD_COMMIT_BUF>::new();
                {
                    let mut i = 0;
                    while i < OOD_DATA_WORDS {
                        ood_buf.data_write(i, read_reduced_field_el::<I>());
                        i += 1;
                    }
                }
                let ood_value: #quartic_struct = unsafe {
                    *ood_buf.data_as::<#quartic_struct>(1).as_ptr()
                };
                ts.commit(&mut ood_buf, OOD_DATA_WORDS);

                read_and_verify_pow::<I>(ts, INITIAL_POW_BITS);
                let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
                    ts, INITIAL_NUM_QUERIES, INITIAL_QUERY_INDEX_BITS,
                    INITIAL_DRAW_WORDS,
                );

                let delinearization_challenge = draw_single_field_el(ts);

                push_whir_pow_entry(accumulator, ood_point, delinearization_challenge);

                let mut claim_correction = ood_value;
                #mul_ood_delin;

                let mut current_delinearization_challenge = delinearization_challenge;

                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[INITIAL_RS_DOMAIN_LOG2];
                let extended_generator_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[INITIAL_RS_DOMAIN_LOG2];
                let mut high_powers_offsets = LazyVec::<#field_struct, MAX_HIGH_POWERS>::new();
                compute_high_powers_offsets(WHIR_FOLD_STEPS[0], &mut high_powers_offsets);
                let mut fold_buf_a = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                fold_buf_a.set_len(FOLD_BUF_HALF);
                let mut fold_buf_b = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                fold_buf_b.set_len(FOLD_BUF_HALF);
                let mut q = 0;
                while q < INITIAL_NUM_QUERIES {
                    #advance_current_delin;

                    let query_index = *query_indices.get(q);
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);
                    let tree_index = compute_tree_index(
                        query_index, NUM_COSETS, NUM_COSETS_LOG2, COSET_TREE_SIZE,
                    );

                    let mut acc0 = #quartic_zero;
                    let mut acc1 = #quartic_zero;

                    #unrolled_oracle_queries

                    let batched_evals = [acc0, acc1];
                    let folded = fold_coset(
                        &batched_evals, WHIR_FOLD_STEPS[0],
                        folding_challenges.as_slice(),
                        base_root_inv, unsafe { high_powers_offsets.as_array::<{1 << (WHIR_FOLD_STEPS[0] - 1)}>() },
                        fold_buf_a.as_mut_slice(), fold_buf_b.as_mut_slice(),
                    );

                    let mut query_point_base = extended_generator.pow(query_index as u32);
                    query_point_base.exp_power_of_2(WHIR_FOLD_STEPS[0]);
                    push_whir_pow_entry(
                        accumulator,
                        <#quartic_struct>::from_base(query_point_base),
                        current_delinearization_challenge,
                    );

                    let mut t = folded;
                    #mul_delin;
                    #add_correction;

                    q += 1;
                }

                #add_claim;

                Ok((claim, intermediate_cap))
            }
        }
    }
}

// ---- Internal Rounds ----

pub fn generate_whir_internal_rounds<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    trace_len_log2: usize,
) -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    let num_internal_rounds = num_rounds - 2;

    let mut poly_size_log2 = trace_len_log2;
    poly_size_log2 -= whir_schedule.whir_steps_schedule[0];

    let mut internal_params: Vec<RoundParams> = Vec::new();
    for i in 0..num_internal_rounds {
        let round_idx = i + 1;
        let lde_factor = whir_schedule.whir_steps_lde_factors[round_idx - 1];
        internal_params.push(round_params(
            whir_schedule,
            round_idx,
            poly_size_log2,
            lde_factor,
        ));
        poly_size_log2 -= whir_schedule.whir_steps_schedule[round_idx];
    }

    let internal_query_index_bits_vec: Vec<usize> =
        internal_params.iter().map(|p| p.query_index_bits).collect();
    let internal_num_cosets_vec: Vec<usize> =
        internal_params.iter().map(|p| p.num_cosets).collect();
    let internal_num_cosets_log2_vec: Vec<usize> =
        internal_params.iter().map(|p| p.num_cosets_log2).collect();
    let internal_coset_tree_size_vec: Vec<usize> =
        internal_params.iter().map(|p| p.coset_tree_size).collect();
    let internal_rs_domain_log2_vec: Vec<usize> =
        internal_params.iter().map(|p| p.rs_domain_log2).collect();
    let internal_draw_words_vec: Vec<usize> =
        internal_params.iter().map(|p| p.draw_words).collect();

    let max_internal_fold_steps = internal_params
        .iter()
        .map(|p| p.fold_steps)
        .max()
        .unwrap_or(1);
    let max_internal_values_per_leaf = 1usize << max_internal_fold_steps;
    let max_internal_fold_buf_half = max_internal_values_per_leaf / 2;
    let max_internal_num_queries = internal_params
        .iter()
        .map(|p| p.num_queries)
        .max()
        .unwrap_or(1);
    let max_internal_draw_words = internal_draw_words_vec.iter().copied().max().unwrap_or(8);

    let num_ir = num_internal_rounds;

    let mul_delin = MW::mul_assign(quote! { t }, quote! { current_delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );
    let advance_current_delin = MW::mul_assign(
        quote! { current_delinearization_challenge },
        quote! { delinearization_challenge },
    );

    let query_body = generate_single_oracle_query_body::<MW>(
        quote! { leaf_ext_words },
        quote! { INTERNAL_HASH_BUF_SIZE },
        quote! { MAX_INTERNAL_VALUES_PER_LEAF },
        quote! { fold_steps },
        quote! { oracle_depth },
        quote! { prev_oracle_cap },
    );

    quote! {
        use super::common::{
            compute_high_powers_offsets, ext_from_raw_word_slice,
            MAX_HIGH_POWERS, EXT_DEGREE,
        };
        use ::verifier_common::whir::{
            hash_leaf_data_into_state, verify_merkle_path,
        };

        pub const NUM_INTERNAL_ROUNDS: usize = #num_ir;
        const INTERNAL_QUERY_INDEX_BITS: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_query_index_bits_vec),*];
        const INTERNAL_NUM_COSETS: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_num_cosets_vec),*];
        const INTERNAL_NUM_COSETS_LOG2: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_num_cosets_log2_vec),*];
        const INTERNAL_COSET_TREE_SIZE: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_coset_tree_size_vec),*];
        const INTERNAL_RS_DOMAIN_LOG2: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_rs_domain_log2_vec),*];
        const MAX_INTERNAL_FOLD_STEPS: usize = #max_internal_fold_steps;
        const MAX_INTERNAL_VALUES_PER_LEAF: usize = #max_internal_values_per_leaf;
        const MAX_INTERNAL_LEAF_EXT_WORDS: usize = MAX_INTERNAL_VALUES_PER_LEAF * EXT_DEGREE;
        const INTERNAL_HASH_BUF_SIZE: usize = MAX_INTERNAL_LEAF_EXT_WORDS.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS;
        const MAX_INTERNAL_FOLD_BUF_HALF: usize = #max_internal_fold_buf_half;
        const MAX_INTERNAL_NUM_QUERIES: usize = #max_internal_num_queries;
        const MAX_INTERNAL_DRAW_WORDS: usize = #max_internal_draw_words;
        const INTERNAL_DRAW_WORDS: [usize; NUM_INTERNAL_ROUNDS] =
            [#(#internal_draw_words_vec),*];

        pub fn verify_internal_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
            ts: &mut TranscriptState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            claim: #quartic_struct,
            prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
            round_idx: usize,
            z_initial: &[#quartic_struct],
            accumulator: &mut ::verifier_common::whir::WhirAccumulator<
                #quartic_struct, MAX_POW_ENTRIES,
            >,
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), E::Error> {
            unsafe {
                let fold_steps = WHIR_FOLD_STEPS[round_idx];
                let num_queries = WHIR_QUERIES[round_idx];
                let values_per_leaf = 1usize << fold_steps;
                let leaf_ext_words = values_per_leaf * EXT_DEGREE;
                let ir = round_idx - 1;

                let mut claim = claim;
                let mut folding_challenges: LazyVec<#quartic_struct, MAX_INTERNAL_FOLD_STEPS> =
                    LazyVec::new();
                let mut round = 0;
                while round < fold_steps {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(
                        ts, claim, round,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    fold_whir_accumulator(accumulator, alpha, z_initial);
                    round += 1;
                }

                const CAP_COMMIT_BUF: usize = {
                    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_CAP_WORDS;
                    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let intermediate_cap =
                    read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(ts);

                let ood_point = draw_single_field_el(ts);

                const OOD_DATA_WORDS: usize = EXT_DEGREE;
                const OOD_COMMIT_BUF: usize = {
                    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + OOD_DATA_WORDS;
                    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let mut ood_buf = CommitBuf::<OOD_COMMIT_BUF>::new();
                {
                    let mut i = 0;
                    while i < OOD_DATA_WORDS {
                        ood_buf.data_write(i, read_reduced_field_el::<I>());
                        i += 1;
                    }
                }
                let ood_value: #quartic_struct = unsafe {
                    *ood_buf.data_as::<#quartic_struct>(1).as_ptr()
                };
                ts.commit(&mut ood_buf, OOD_DATA_WORDS);

                read_and_verify_pow::<I>(ts, WHIR_POW_BITS[round_idx]);
                let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
                let draw_words = INTERNAL_DRAW_WORDS[ir];
                let query_indices =
                    draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
                        ts, num_queries, query_index_bits, draw_words,
                    );

                let delinearization_challenge = draw_single_field_el(ts);

                push_whir_pow_entry(accumulator, ood_point, delinearization_challenge);

                let mut claim_correction = ood_value;
                #mul_ood_delin;

                let mut current_delinearization_challenge = delinearization_challenge;

                let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[rs_domain_log2];
                let extended_generator_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[rs_domain_log2];
                let num_cosets = INTERNAL_NUM_COSETS[ir];
                let num_cosets_log2 = INTERNAL_NUM_COSETS_LOG2[ir];
                let coset_tree_size = INTERNAL_COSET_TREE_SIZE[ir];
                let oracle_depth = WHIR_ORACLE_DEPTHS[round_idx - 1];

                let mut high_powers_offsets = LazyVec::<#field_struct, MAX_HIGH_POWERS>::new();
                compute_high_powers_offsets(fold_steps, &mut high_powers_offsets);

                let mut fold_buf_a = LazyVec::<#quartic_struct, MAX_INTERNAL_FOLD_BUF_HALF>::new();
                fold_buf_a.set_len(MAX_INTERNAL_FOLD_BUF_HALF);
                let mut fold_buf_b = LazyVec::<#quartic_struct, MAX_INTERNAL_FOLD_BUF_HALF>::new();
                fold_buf_b.set_len(MAX_INTERNAL_FOLD_BUF_HALF);
                let mut q = 0;
                while q < num_queries {
                    #advance_current_delin;

                    let query_index = *query_indices.get(q);
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);
                    let tree_index = compute_tree_index(
                        query_index, num_cosets, num_cosets_log2, coset_tree_size,
                    );

                    #query_body

                    let mut query_point_base = extended_generator.pow(query_index as u32);
                    query_point_base.exp_power_of_2(fold_steps);
                    push_whir_pow_entry(
                        accumulator,
                        <#quartic_struct>::from_base(query_point_base),
                        current_delinearization_challenge,
                    );

                    let mut t = folded;
                    #mul_delin;
                    #add_correction;

                    q += 1;
                }

                #add_claim;

                Ok((claim, intermediate_cap))
            }
        }
    }
}

// ---- Final Round ----

pub fn generate_whir_final_round<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    trace_len_log2: usize,
) -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let horner_mul = MW::mul_assign_by_base(quote! { eval }, quote! { query_point });
    let horner_add = MW::add_assign(quote! { eval }, quote! { coeff });

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    let final_round_idx = num_rounds - 1;

    let mut poly_size_log2 = trace_len_log2;
    for i in 0..final_round_idx {
        poly_size_log2 -= whir_schedule.whir_steps_schedule[i];
    }
    let lde_factor = whir_schedule.whir_steps_lde_factors[final_round_idx - 1];
    let params = round_params(whir_schedule, final_round_idx, poly_size_log2, lde_factor);

    let fold_steps = params.fold_steps;
    let values_per_leaf = params.values_per_leaf;
    let num_queries = params.num_queries;
    let fold_buf_half = values_per_leaf / 2;
    let query_index_bits = params.query_index_bits;
    let rs_domain_log2 = params.rs_domain_log2;
    let num_cosets = params.num_cosets;
    let num_cosets_log2 = params.num_cosets_log2;
    let coset_tree_size = params.coset_tree_size;
    let draw_words = params.draw_words;
    let pow_bits = params.pow_bits;
    let last_oracle_depth_idx = final_round_idx - 1;

    let query_body = generate_single_oracle_query_body::<MW>(
        quote! { FINAL_LEAF_EXT_WORDS },
        quote! { FINAL_HASH_BUF_SIZE },
        quote! { FINAL_VALUES_PER_LEAF },
        quote! { FINAL_FOLD_STEPS },
        quote! { oracle_depth },
        quote! { prev_oracle_cap },
    );

    quote! {
        const FINAL_FOLD_STEPS: usize = #fold_steps;
        const FINAL_NUM_QUERIES: usize = #num_queries;
        const FINAL_VALUES_PER_LEAF: usize = #values_per_leaf;
        const FINAL_LEAF_EXT_WORDS: usize = FINAL_VALUES_PER_LEAF * EXT_DEGREE;
        const FINAL_HASH_BUF_SIZE: usize = FINAL_LEAF_EXT_WORDS.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS;
        const FINAL_FOLD_BUF_HALF: usize = #fold_buf_half;
        const FINAL_QUERY_INDEX_BITS: usize = #query_index_bits;
        const FINAL_RS_DOMAIN_LOG2: usize = #rs_domain_log2;
        const FINAL_NUM_COSETS: usize = #num_cosets;
        const FINAL_NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const FINAL_COSET_TREE_SIZE: usize = #coset_tree_size;
        const FINAL_DRAW_WORDS: usize = #draw_words;
        const FINAL_POW_BITS: u32 = #pow_bits;
        const FINAL_ORACLE_DEPTH_IDX: usize = #last_oracle_depth_idx;

        pub fn verify_final_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
            ts: &mut TranscriptState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            claim: #quartic_struct,
            prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
            z_initial: &[#quartic_struct],
            accumulator: &mut ::verifier_common::whir::WhirAccumulator<
                #quartic_struct, MAX_POW_ENTRIES,
            >,
        ) -> Result<(), E::Error> {
            unsafe {
                let mut claim = claim;
                let mut folding_challenges: LazyVec<#quartic_struct, FINAL_FOLD_STEPS> =
                    LazyVec::new();
                let mut round = 0;
                while round < FINAL_FOLD_STEPS {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(
                        ts, claim, round,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    fold_whir_accumulator(accumulator, alpha, z_initial);
                    round += 1;
                }

                debug_assert_eq!(
                    accumulator.z_initial_idx + FINAL_MONOMIALS_LEN.trailing_zeros() as usize,
                    z_initial.len(),
                );
                debug_assert_eq!(accumulator.pow_entries.len(), MAX_POW_ENTRIES);

                const FINAL_MONOMIALS_DATA_WORDS: usize = FINAL_MONOMIALS_LEN * EXT_DEGREE;
                const FINAL_MONOMIALS_COMMIT_BUF: usize = {
                    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + FINAL_MONOMIALS_DATA_WORDS;
                    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let mut monomials_buf = CommitBuf::<FINAL_MONOMIALS_COMMIT_BUF>::new();
                {
                    let mut i = 0;
                    while i < FINAL_MONOMIALS_DATA_WORDS {
                        monomials_buf.data_write(i, read_reduced_field_el::<I>());
                        i += 1;
                    }
                }
                ts.commit(&mut monomials_buf, FINAL_MONOMIALS_DATA_WORDS);
                let monomials: &[#quartic_struct] = monomials_buf.data_as::<#quartic_struct>(FINAL_MONOMIALS_LEN);

                read_and_verify_pow::<I>(ts, FINAL_POW_BITS);
                let query_indices =
                    draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
                        ts, FINAL_NUM_QUERIES, FINAL_QUERY_INDEX_BITS, FINAL_DRAW_WORDS,
                    );

                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[FINAL_RS_DOMAIN_LOG2];
                let extended_generator_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[FINAL_RS_DOMAIN_LOG2];
                let oracle_depth = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];

                let mut high_powers_offsets = LazyVec::<#field_struct, MAX_HIGH_POWERS>::new();
                compute_high_powers_offsets(FINAL_FOLD_STEPS, &mut high_powers_offsets);

                let mut fold_buf_a = LazyVec::<#quartic_struct, FINAL_FOLD_BUF_HALF>::new();
                fold_buf_a.set_len(FINAL_FOLD_BUF_HALF);
                let mut fold_buf_b = LazyVec::<#quartic_struct, FINAL_FOLD_BUF_HALF>::new();
                fold_buf_b.set_len(FINAL_FOLD_BUF_HALF);
                let mut folded_values: LazyVec<#quartic_struct, FINAL_NUM_QUERIES> =
                    LazyVec::new();
                let mut query_base_roots: LazyVec<#field_struct, FINAL_NUM_QUERIES> =
                    LazyVec::new();

                let mut q = 0;
                while q < FINAL_NUM_QUERIES {
                    let query_index = *query_indices.get(q);
                    let base_root = extended_generator.pow(query_index as u32);
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);

                    let tree_index = compute_tree_index(
                        query_index, FINAL_NUM_COSETS, FINAL_NUM_COSETS_LOG2, FINAL_COSET_TREE_SIZE,
                    );

                    #query_body

                    folded_values.push(folded);
                    query_base_roots.push(base_root);

                    q += 1;
                }


                let mut q = 0;
                while q < FINAL_NUM_QUERIES {
                    let mut query_point = *query_base_roots.get(q);
                    query_point.exp_power_of_2(FINAL_FOLD_STEPS);

                    let mut eval = *monomials.get_unchecked(FINAL_MONOMIALS_LEN - 1);
                    let mut j = FINAL_MONOMIALS_LEN - 1;
                    while j > 0 {
                        j -= 1;
                        #horner_mul;
                        let coeff = *monomials.get_unchecked(j);
                        #horner_add;
                    }

                    if eval != *folded_values.get(q) {
                        return Err(E::whir_fold_agreement_failed(q));
                    }
                    q += 1;
                }

                let mut f_m_buf = LazyVec::<#quartic_struct, FINAL_MONOMIALS_LEN>::new();
                f_m_buf.set_len(FINAL_MONOMIALS_LEN);
                {
                    let mut i = 0;
                    while i < FINAL_MONOMIALS_LEN {
                        f_m_buf.set_unchecked(i, *monomials.get_unchecked(i));
                        i += 1;
                    }
                }
                {
                    let mut level = 0;
                    let mut active_len = FINAL_MONOMIALS_LEN;
                    while active_len > 1 {
                        let half = active_len >> 1;
                        let zj = *z_initial.get_unchecked(accumulator.z_initial_idx + level);
                        let mut i = 0;
                        while i < half {
                            let c0 = *f_m_buf.get_unchecked(2 * i);
                            let c1 = *f_m_buf.get_unchecked(2 * i + 1);
                            let mut t = c1;
                            field_ops::mul_assign(&mut t, &zj);
                            field_ops::add_assign(&mut t, &c0);
                            f_m_buf.set_unchecked(i, t);
                            i += 1;
                        }
                        active_len = half;
                        level += 1;
                    }
                }
                let f_m_at_z_initial = *f_m_buf.get_unchecked(0);

                let mut expected = accumulator.z_initial_prefactor;
                field_ops::mul_assign(&mut expected, &f_m_at_z_initial);

                {
                    let n = accumulator.pow_entries.len();
                    let mut ei = 0;
                    while ei < n {
                        let entry = accumulator.pow_entries.get_unchecked(ei);
                        let s = entry.current_scalar;
                        let mut eval = *monomials.get_unchecked(FINAL_MONOMIALS_LEN - 1);
                        let mut j = FINAL_MONOMIALS_LEN - 1;
                        while j > 0 {
                            j -= 1;
                            field_ops::mul_assign(&mut eval, &s);
                            let coeff = *monomials.get_unchecked(j);
                            field_ops::add_assign(&mut eval, &coeff);
                        }
                        field_ops::mul_assign(&mut eval, &entry.prefactor);
                        field_ops::mul_assign(&mut eval, &entry.coefficient);
                        field_ops::add_assign(&mut expected, &eval);
                        ei += 1;
                    }
                }

                if expected != claim {
                    return Err(E::whir_final_constraint_failed());
                }

                Ok(())
            }
        }
    }
}
