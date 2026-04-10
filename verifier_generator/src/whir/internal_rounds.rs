use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::gkr::prover::WhirSchedule;

pub fn generate_whir_internal_rounds<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    trace_len_log2: usize,
) -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    let num_internal_rounds = num_rounds - 2; // exclude initial (0) and final (last)

    let mut internal_query_index_bits_vec = Vec::with_capacity(num_internal_rounds);
    let mut internal_num_cosets_vec = Vec::with_capacity(num_internal_rounds);
    let mut internal_num_cosets_log2_vec = Vec::with_capacity(num_internal_rounds);
    let mut internal_coset_tree_size_vec = Vec::with_capacity(num_internal_rounds);
    let mut internal_rs_domain_log2_vec = Vec::with_capacity(num_internal_rounds);

    let mut poly_size_log2 = trace_len_log2;
    poly_size_log2 -= whir_schedule.whir_steps_schedule[0]; // after initial round

    for i in 0..num_internal_rounds {
        let round_idx = i + 1;
        let fold_steps = whir_schedule.whir_steps_schedule[round_idx];
        let lde_factor = whir_schedule.whir_steps_lde_factors[round_idx - 1];
        let lde_factor_log2 = lde_factor.trailing_zeros() as usize;
        let rs_domain = poly_size_log2 + lde_factor_log2;
        let query_domain = rs_domain - fold_steps;
        let values_per_leaf = 1usize << fold_steps;
        let coset_tree = (1usize << poly_size_log2) / values_per_leaf;

        internal_query_index_bits_vec.push(query_domain);
        internal_num_cosets_vec.push(lde_factor);
        internal_num_cosets_log2_vec.push(lde_factor_log2);
        internal_coset_tree_size_vec.push(coset_tree);
        internal_rs_domain_log2_vec.push(rs_domain);

        poly_size_log2 -= fold_steps;
    }

    let internal_fold_steps_range = &whir_schedule.whir_steps_schedule[1..num_rounds - 1];
    let internal_queries_range = &whir_schedule.whir_queries_schedule[1..num_rounds - 1];

    let max_internal_fold_steps = *internal_fold_steps_range.iter().max().unwrap_or(&1);
    let max_internal_values_per_leaf = 1usize << max_internal_fold_steps;
    let max_internal_leaf_ext_words = max_internal_values_per_leaf * 4; // EXT_DEGREE=4
    let internal_hash_buf_size = max_internal_leaf_ext_words.div_ceil(16) * 16;
    let max_internal_fold_buf_half = max_internal_values_per_leaf / 2;
    let max_internal_num_queries = *internal_queries_range.iter().max().unwrap_or(&1);
    let internal_draw_words_vec: Vec<usize> = internal_query_index_bits_vec
        .iter()
        .enumerate()
        .map(|(i, &bits)| {
            let nq = whir_schedule.whir_queries_schedule[i + 1];
            let total_bits = nq * bits + 32;
            total_bits.div_ceil(256) * 8
        })
        .collect();
    let max_internal_draw_words = *internal_draw_words_vec.iter().max().unwrap_or(&8);

    let num_ir = num_internal_rounds;

    let mul_delin = MW::mul_assign(quote! { t }, quote! { delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );

    quote! {
        use super::common::{
            compute_high_powers_offsets, ext_from_raw_words,
            MAX_HIGH_POWERS, EXT_DEGREE,
        };
        use ::verifier_common::whir::{
            read_return_merkle_cap, hash_leaf_data_into_state, verify_merkle_path,
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
        const INTERNAL_HASH_BUF_SIZE: usize = #internal_hash_buf_size;
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
                    round += 1;
                }

                let intermediate_cap =
                    read_return_merkle_cap::<I, WHIR_CAP_WORDS>();

                let _ood_point = draw_single_field_el(ts);
                let ood_value: #quartic_struct = read_field_el::<I>();

                read_and_verify_pow::<I>(ts, WHIR_POW_BITS[round_idx]);
                let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
                let draw_words = INTERNAL_DRAW_WORDS[ir];
                let query_indices =
                    draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
                        ts, num_queries, query_index_bits, draw_words,
                    );

                let delinearization_challenge = draw_single_field_el(ts);

                let mut claim_correction = ood_value;
                #mul_ood_delin;

                let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
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
                    let query_index = *query_indices.get(q);
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);

                    let tree_index = compute_tree_index(
                        query_index, num_cosets, num_cosets_log2, coset_tree_size,
                    );

                    {
                        let mut i = 0;
                        while i < leaf_ext_words {
                            hash_buf.write(i, read_reduced_field_el::<I>());
                            i += 1;
                        }
                    }
                    let block_end = leaf_ext_words.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
                    hash_buf.zero_range(leaf_ext_words, block_end);

                    let init_buf = hash_buf.assume_init_subarray::<INTERNAL_HASH_BUF_SIZE>();
                    hash_leaf_data_into_state(&mut ts.hasher, init_buf, leaf_ext_words);
                    if !verify_merkle_path::<I>(
                        &mut ts.hasher, tree_index, oracle_depth, prev_oracle_cap,
                    ) {
                        return Err(E::whir_merkle_path_failed(q));
                    }

                    let mut evals: LazyVec<#quartic_struct, MAX_INTERNAL_VALUES_PER_LEAF> =
                        LazyVec::new();
                    let mut j = 0;
                    while j < values_per_leaf {
                        evals.push(ext_from_raw_words(
                            &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
                        ));
                        j += 1;
                    }

                    let folded = fold_coset(
                        evals.as_slice(), fold_steps,
                        folding_challenges.as_slice(),
                        base_root_inv, high_powers_offsets.as_slice(),
                        fold_buf_a.as_mut_slice(), fold_buf_b.as_mut_slice(),
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
