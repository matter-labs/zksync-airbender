use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::gkr::prover::WhirSchedule;

/// Generate per-circuit WHIR verifier code (initial round).
pub fn generate_whir_inlined<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    num_mem_oracle_cols: usize,
    num_wit_oracle_cols: usize,
    num_setup_oracle_cols: usize,
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

    // draw_words for query bit generation
    let total_bits_needed = initial_num_queries * query_index_bits + 32;
    let draw_words = total_bits_needed.div_ceil(256) * 8;

    // Leaf sizes per oracle (in u32 words) — uses actual oracle column counts
    let mem_leaf_words = num_mem_oracle_cols * values_per_leaf;
    let wit_leaf_words = num_wit_oracle_cols * values_per_leaf;
    let setup_leaf_words = num_setup_oracle_cols * values_per_leaf;
    let max_leaf_words = mem_leaf_words.max(wit_leaf_words).max(setup_leaf_words);
    // Padded to BLAKE2S_BLOCK_SIZE_U32_WORDS (16) boundary for aligned hashing
    let hash_buf_padded = max_leaf_words.div_ceil(16) * 16;
    let fold_buf_half = values_per_leaf / 2;

    // MW operations
    let batch_mul_local_0 = MW::mul_assign_by_base(quote! { term }, quote! { base_val });
    let batch_add_acc0 = MW::add_assign(quote! { *acc0 }, quote! { term });
    let batch_mul_local_1 = MW::mul_assign_by_base(quote! { term }, quote! { base_val });
    let batch_add_acc1 = MW::add_assign(quote! { *acc1 }, quote! { term });
    let mul_delin = MW::mul_assign(quote! { t }, quote! { delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );
    let degree = 4usize; // EXT_DEGREE for BabyBear/Mersenne31 quartic
    let digest_words = 8usize; // BLAKE2S_DIGEST_SIZE_U32_WORDS
    let block_words = 16usize; // BLAKE2S_BLOCK_SIZE_U32_WORDS
    let ood_data_words = degree;
    let ood_commit_buf_size = (digest_words + ood_data_words).div_ceil(block_words) * block_words;

    let from_raw_0 = MW::field_from_reduced_raw_repr(quote! { raw0 });
    let from_raw_1 = MW::field_from_reduced_raw_repr(quote! { raw1 });
    let batch_mul_eval = MW::mul_assign(quote! { term }, quote! { eval });
    let add_claim_eval = MW::add_assign(quote! { claim }, quote! { term });

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
            draw_query_indices, verify_merkle_path, hash_leaf_data_into_state,
        };
        use super::common::{
            verify_whir_sumcheck_step, fold_coset, materialize_gamma_powers,
            WhirVerificationError, read_field_el, read_field_els,
            read_reduced_field_el, draw_single_field_el, compute_tree_index,
        };
        use ::verifier_common::structs::CommitBuf;
        use super::constants::*;

        const INITIAL_VALUES_PER_LEAF: usize = #values_per_leaf;
        const INITIAL_QUERY_INDEX_BITS: usize = #query_index_bits;
        const INITIAL_NUM_QUERIES: usize = #initial_num_queries;
        const INITIAL_POW_BITS: u32 = #initial_pow_bits;
        const INITIAL_DRAW_WORDS: usize = #draw_words;
        const INITIAL_RS_DOMAIN_LOG2: usize = #rs_domain_log2;
        const MEM_LEAF_WORDS: usize = #mem_leaf_words;
        const WIT_LEAF_WORDS: usize = #wit_leaf_words;
        const SETUP_LEAF_WORDS: usize = #setup_leaf_words;
        const HASH_BUF_SIZE: usize = #hash_buf_padded;
        const FOLD_BUF_HALF: usize = #fold_buf_half;
        const NUM_COSETS: usize = #num_cosets;
        const NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const COSET_TREE_SIZE: usize = #coset_tree_size;

        /// Read leaf data from NDS into hash_buf and batch into accumulators
        /// in a single pass. NDS is column-major (matching Merkle hash layout).
        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        unsafe fn read_and_batch_leaf<I: NonDeterminismSource>(
            hash_buf: &mut [u32],
            num_columns: usize,
            gamma_powers: &[#quartic_struct],
            gamma_offset: usize,
            acc0: &mut #quartic_struct,
            acc1: &mut #quartic_struct,
        ) {
            let mut col = 0;
            while col < num_columns {
                let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
                let idx = col * 2;

                let raw0 = read_reduced_field_el::<I>();
                *hash_buf.get_unchecked_mut(idx) = raw0;
                let base_val = #from_raw_0;
                let mut term = gamma;
                #batch_mul_local_0;
                #batch_add_acc0;

                let raw1 = read_reduced_field_el::<I>();
                *hash_buf.get_unchecked_mut(idx + 1) = raw1;
                let base_val = #from_raw_1;
                let mut term = gamma;
                #batch_mul_local_1;
                #batch_add_acc1;

                col += 1;
            }
        }

        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        unsafe fn process_oracle_query<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            num_columns: usize,
            leaf_words: usize,
            query_index: usize,
            depth: usize,
            cap: &[u32],
            gamma_powers: &[#quartic_struct],
            gamma_offset: usize,
            acc0: &mut #quartic_struct,
            acc1: &mut #quartic_struct,
            query: usize,
        ) -> Result<(), WhirVerificationError> {
            let buf = hash_buf.assume_init_subarray_mut::<HASH_BUF_SIZE>();
            read_and_batch_leaf::<I>(
                &mut buf[..leaf_words], num_columns,
                gamma_powers, gamma_offset, acc0, acc1,
            );

            // Zero the tail of the last Blake2s block for hash padding.
            let block_end = leaf_words.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            if block_end > leaf_words {
                hash_buf.zero_range(leaf_words, block_end);
            }
            let buf = hash_buf.assume_init_subarray::<HASH_BUF_SIZE>();
            hash_leaf_data_into_state(hasher, buf, leaf_words);
            if !verify_merkle_path::<I>(hasher, query_index, depth, cap) {
                return Err(WhirVerificationError::MerklePathFailed { query });
            }
            Ok(())
        }

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe, clippy::needless_borrow)]
        pub fn verify_initial_whir_round<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            seed: &mut Seed,
            batching_challenge: #quartic_struct,
            setup_cap: &[u32; SETUP_CAP_WORDS],
            memory_cap: &[u32; MEM_CAP_WORDS],
            witness_cap: &[u32; WIT_CAP_WORDS],
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
            unsafe {

                // --- 0. Read all oracle evals from NDS and batch ---
                // The prover provides evals for ALL oracle columns (not just GKR base layer).
                // These are NOT committed to the transcript — same as the prover.
                let gamma_powers: [#quartic_struct; TOTAL_ORACLE_COLS] =
                    materialize_gamma_powers(batching_challenge);
                let mut claim = #quartic_zero;
                {
                    let mut col_idx = 0;
                    // Memory evals
                    let mut i = 0;
                    while i < NUM_MEM_ORACLE_COLS {
                        let eval: #quartic_struct = read_field_el::<I>();
                        let mut term = unsafe { *gamma_powers.get_unchecked(col_idx) };
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                        i += 1;
                    }
                    // Witness evals
                    i = 0;
                    while i < NUM_WIT_ORACLE_COLS {
                        let eval: #quartic_struct = read_field_el::<I>();
                        let mut term = unsafe { *gamma_powers.get_unchecked(col_idx) };
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                        i += 1;
                    }
                    // Setup evals
                    i = 0;
                    while i < NUM_SETUP_ORACLE_COLS {
                        let eval: #quartic_struct = read_field_el::<I>();
                        let mut term = unsafe { *gamma_powers.get_unchecked(col_idx) };
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                        i += 1;
                    }
                }

                // --- 1. Sumcheck folds ---
                let mut folding_challenges: LazyVec<#quartic_struct, { WHIR_FOLD_STEPS[0] }> =
                    LazyVec::new();
                let mut round_idx = 0;
                while round_idx < WHIR_FOLD_STEPS[0] {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I>(
                        hasher, seed, claim, round_idx,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    round_idx += 1;
                }

                // --- 2. Read and commit intermediate oracle cap ---
                const CAP_COMMIT_BUF: usize = {
                    let total = ::verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_CAP_WORDS;
                    (total + ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
                        * ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
                };
                let intermediate_cap =
                    read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(
                        hasher, seed,
                    );

                // --- 3. OOD: draw point, read value, commit ---
                // ood_point advances the Fiat-Shamir transcript; the verifier does not
                // use its value directly — the OOD evaluation is checked implicitly
                // through the next round's sumcheck claim.
                let _ood_point = draw_single_field_el(hasher, seed);

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
                ood_buf.commit(hasher, seed, #ood_data_words);

                // --- 4. PoW + query indices ---
                read_and_verify_pow::<I>(seed, INITIAL_POW_BITS);
                let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
                    hasher, seed, INITIAL_NUM_QUERIES, INITIAL_QUERY_INDEX_BITS,
                    INITIAL_DRAW_WORDS,
                );

                // --- 5. Delinearization challenge ---
                let delinearization_challenge = draw_single_field_el(hasher, seed);

                // --- 6. Claim correction: starts with OOD contribution ---
                let mut claim_correction = ood_value;
                #mul_ood_delin;

                // --- 7. Per-query processing ---
                let extended_generator_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[INITIAL_RS_DOMAIN_LOG2];
                let mut high_powers_offsets = LazyVec::<#field_struct, MAX_HIGH_POWERS>::new();
                compute_high_powers_offsets(WHIR_FOLD_STEPS[0], &mut high_powers_offsets);
                // Scratch buffers — fully written before read each iteration
                let mut fold_buf_a = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                unsafe { fold_buf_a.set_len(FOLD_BUF_HALF); }
                let mut fold_buf_b = LazyVec::<#quartic_struct, FOLD_BUF_HALF>::new();
                unsafe { fold_buf_b.set_len(FOLD_BUF_HALF); }
                let mut q = 0;
                while q < INITIAL_NUM_QUERIES {
                    let query_index = *query_indices.get(q);

                    // query_index determines omega^k for the algebraic fold
                    let base_root_inv = extended_generator_inv.pow(query_index as u32);

                    // Tree leaves are stored sequentially by coset (with bit-reversed
                    // coset ordering).  Map from the interleaved query_index to the
                    // actual tree leaf position.
                    let tree_index = compute_tree_index(
                        query_index, NUM_COSETS, NUM_COSETS_LOG2, COSET_TREE_SIZE,
                    );

                    // Accumulators across 3 oracles — zero-init is semantic
                    let mut acc0 = #quartic_zero;
                    let mut acc1 = #quartic_zero;

                    // Memory oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_MEM_ORACLE_COLS, MEM_LEAF_WORDS, tree_index,
                        BASE_ORACLE_DEPTH, memory_cap, &gamma_powers[..], 0,
                        &mut acc0, &mut acc1, q,
                    )?;
                    // Witness oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_WIT_ORACLE_COLS, WIT_LEAF_WORDS, tree_index,
                        BASE_ORACLE_DEPTH, witness_cap, &gamma_powers[..], NUM_MEM_ORACLE_COLS,
                        &mut acc0, &mut acc1, q,
                    )?;
                    // Setup oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_SETUP_ORACLE_COLS, SETUP_LEAF_WORDS, tree_index,
                        SETUP_ORACLE_DEPTH, setup_cap, &gamma_powers[..],
                        NUM_MEM_ORACLE_COLS + NUM_WIT_ORACLE_COLS,
                        &mut acc0, &mut acc1, q,
                    )?;

                    // Fold
                    let batched_evals = [acc0, acc1];
                    let folded = fold_coset(
                        &batched_evals, WHIR_FOLD_STEPS[0],
                        folding_challenges.as_slice(),
                        base_root_inv, unsafe { high_powers_offsets.as_array::<{1 << (WHIR_FOLD_STEPS[0] - 1)}>() },
                        fold_buf_a.as_mut_slice(), fold_buf_b.as_mut_slice(),
                    );

                    // Accumulate claim correction
                    let mut t = folded;
                    #mul_delin;
                    #add_correction;

                    q += 1;
                }

                // --- 8. Update claim ---
                #add_claim;

                Ok((claim, intermediate_cap))
            }
        }
    }
}
