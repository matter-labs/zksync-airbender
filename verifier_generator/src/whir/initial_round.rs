use proc_macro2::TokenStream;
use quote::quote;

use crate::gkr::OracleInfo;
use crate::mersenne_wrapper::MersenneWrapper;
use prover::gkr::prover::WhirSchedule;

pub fn generate_whir_inlined<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    oracles: &[OracleInfo],
    trace_len_log2: usize,
) -> TokenStream {
    let field_use_stmts = MW::field_use_statements();
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();

    let initial_fold_steps = whir_schedule.whir_steps_schedule[0];
    let values_per_leaf = 1usize << initial_fold_steps;
    let base_lde_factor = whir_schedule.base_lde_factor;
    let base_lde_factor_log2 = base_lde_factor.trailing_zeros() as usize;
    let rs_domain_log2 = trace_len_log2 + base_lde_factor_log2;
    let query_domain_log2 = rs_domain_log2 - initial_fold_steps;
    let query_index_bits = query_domain_log2;
    let num_cosets = base_lde_factor;
    let num_cosets_log2 = base_lde_factor_log2;
    let coset_tree_size = (1usize << trace_len_log2) / values_per_leaf;
    let initial_num_queries = whir_schedule.whir_queries_schedule[0];
    let initial_pow_bits = whir_schedule.whir_pow_schedule[0];

    let total_bits_needed = initial_num_queries * query_index_bits + 32;
    let draw_words = total_bits_needed.div_ceil(256) * 8;

    let oracle_leaf_words: Vec<usize> = oracles
        .iter()
        .map(|o| o.num_columns * values_per_leaf)
        .collect();
    let max_leaf_words = oracle_leaf_words.iter().copied().max().unwrap_or(0);
    let hash_buf_padded = max_leaf_words.div_ceil(16) * 16;
    let fold_buf_half = values_per_leaf / 2;

    let mul_delin = MW::mul_assign(quote! { t }, quote! { delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );
    let batch_mul_eval = MW::mul_assign(quote! { term }, quote! { eval });
    let add_claim_eval = MW::add_assign(quote! { claim }, quote! { term });

    let degree = 4usize;
    let digest_words = 8usize;
    let block_words = 16usize;
    let ood_data_words = degree;
    let ood_commit_buf_size = (digest_words + ood_data_words).div_ceil(block_words) * block_words;

    quote! {
        #field_use_stmts
        use core::mem::MaybeUninit;
        use ::verifier_common::field::{Field, PrimeField};
        use ::verifier_common::field_ops;
        use ::verifier_common::transcript::Seed;
        use ::verifier_common::blake2s_u32::{
            AlignedArray64, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
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
            WhirVerificationError, read_field_el, read_field_els,
            read_reduced_field_el, draw_single_field_el, compute_tree_index,
            read_and_batch_leaf, process_oracle_query,
        };
        use ::verifier_common::structs::{CommitBuf, TranscriptState};
        use super::constants::*;

        const INITIAL_VALUES_PER_LEAF: usize = #values_per_leaf;
        const INITIAL_QUERY_INDEX_BITS: usize = #query_index_bits;
        const INITIAL_NUM_QUERIES: usize = #initial_num_queries;
        const INITIAL_POW_BITS: u32 = #initial_pow_bits;
        const INITIAL_DRAW_WORDS: usize = #draw_words;
        const INITIAL_RS_DOMAIN_LOG2: usize = #rs_domain_log2;
        const ORACLE_LEAF_WORDS: [usize; NUM_ORACLES] = [#(#oracle_leaf_words),*];
        const HASH_BUF_SIZE: usize = #hash_buf_padded;
        const FOLD_BUF_HALF: usize = #fold_buf_half;
        const NUM_COSETS: usize = #num_cosets;
        const NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const COSET_TREE_SIZE: usize = #coset_tree_size;

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe, clippy::needless_borrow)]
        pub fn verify_initial_whir_round<I: NonDeterminismSource>(
            ts: &mut TranscriptState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            batching_challenge: #quartic_struct,
            oracle_caps: &[u32; TOTAL_CAP_WORDS],
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
            unsafe {

                let gamma_powers: [#quartic_struct; TOTAL_ORACLE_COLS] =
                    materialize_gamma_powers(batching_challenge);
                let mut claim = #quartic_zero;
                {
                    let mut col_idx = 0;
                    let mut oracle_idx = 0;
                    while oracle_idx < NUM_ORACLES {
                        let num_cols = ORACLE_NUM_COLS[oracle_idx];
                        let mut i = 0;
                        while i < num_cols {
                            let eval: #quartic_struct = read_field_el::<I>();
                            let mut term = unsafe { *gamma_powers.get_unchecked(col_idx) };
                            #batch_mul_eval;
                            #add_claim_eval;
                            col_idx += 1;
                            i += 1;
                        }
                        oracle_idx += 1;
                    }
                }

                let mut folding_challenges: LazyVec<#quartic_struct, { WHIR_FOLD_STEPS[0] }> =
                    LazyVec::new();
                let mut round_idx = 0;
                while round_idx < WHIR_FOLD_STEPS[0] {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I>(
                        ts, claim, round_idx,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    round_idx += 1;
                }

                const CAP_COMMIT_BUF: usize = {
                    let total = ::verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_CAP_WORDS;
                    (total + ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let intermediate_cap =
                    read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(
                        ts,
                    );

                let _ood_point = draw_single_field_el(ts);

                let mut ood_buf = CommitBuf::<#ood_commit_buf_size>::new();
                {
                    let mut i = 0;
                    while i < #ood_data_words {
                        ood_buf.data_write(i, read_reduced_field_el::<I>());
                        i += 1;
                    }
                }
                let ood_value: #quartic_struct = unsafe {
                    *ood_buf.data_as::<#quartic_struct>(1).as_ptr()
                };
                ts.commit(&mut ood_buf, #ood_data_words);

                read_and_verify_pow::<I>(ts, INITIAL_POW_BITS);
                let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
                    ts, INITIAL_NUM_QUERIES, INITIAL_QUERY_INDEX_BITS,
                    INITIAL_DRAW_WORDS,
                );

                let delinearization_challenge = draw_single_field_el(ts);

                let mut claim_correction = ood_value;
                #mul_ood_delin;

                let extended_generator_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[INITIAL_RS_DOMAIN_LOG2];
                let mut high_powers_offsets = LazyVec::<#field_struct, MAX_HIGH_POWERS>::new();
                compute_high_powers_offsets(WHIR_FOLD_STEPS[0], &mut high_powers_offsets);
                let mut fold_buf_a = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                unsafe { fold_buf_a.set_len(FOLD_BUF_HALF); }
                let mut fold_buf_b = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                unsafe { fold_buf_b.set_len(FOLD_BUF_HALF); }
                let mut q = 0;
                while q < INITIAL_NUM_QUERIES {
                    let query_index = *query_indices.get(q);
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);
                    let tree_index = compute_tree_index(
                        query_index, NUM_COSETS, NUM_COSETS_LOG2, COSET_TREE_SIZE,
                    );

                    let mut acc0 = #quartic_zero;
                    let mut acc1 = #quartic_zero;

                    let mut gamma_offset = 0usize;
                    let mut cap_offset = 0usize;
                    let mut oracle_idx = 0;
                    while oracle_idx < NUM_ORACLES {
                        let num_cols = ORACLE_NUM_COLS[oracle_idx];
                        let leaf_words = ORACLE_LEAF_WORDS[oracle_idx];
                        let cap_words = ORACLE_CAP_WORDS[oracle_idx];
                        let depth = ORACLE_DEPTHS[oracle_idx];

                        if num_cols > 0 {
                            process_oracle_query::<I, WHIR_HASH_BUF_SIZE>(
                                &mut ts.hasher, hash_buf,
                                num_cols, leaf_words, tree_index,
                                depth,
                                &oracle_caps[cap_offset..cap_offset + cap_words],
                                &gamma_powers[..], gamma_offset,
                                &mut acc0, &mut acc1, q,
                            )?;
                        }
                        gamma_offset += num_cols;
                        cap_offset += cap_words;
                        oracle_idx += 1;
                    }

                    let batched_evals = [acc0, acc1];
                    let folded = fold_coset(
                        &batched_evals, WHIR_FOLD_STEPS[0],
                        folding_challenges.as_slice(),
                        base_root_inv, unsafe { high_powers_offsets.as_array::<{1 << (WHIR_FOLD_STEPS[0] - 1)}>() },
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
