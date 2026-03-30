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
    let field_one = MW::field_one();

    let initial_fold_steps = whir_schedule.whir_steps_schedule[0];
    let values_per_leaf = 1usize << initial_fold_steps;
    let total_oracle_cols = num_mem_oracle_cols + num_wit_oracle_cols + num_setup_oracle_cols;

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
    let draw_words = ((total_bits_needed + 255) / 256) * 8;

    // Leaf sizes per oracle (in u32 words) — uses actual oracle column counts
    let mem_leaf_words = num_mem_oracle_cols * values_per_leaf;
    let wit_leaf_words = num_wit_oracle_cols * values_per_leaf;
    let setup_leaf_words = num_setup_oracle_cols * values_per_leaf;
    let max_leaf_words = mem_leaf_words.max(wit_leaf_words).max(setup_leaf_words);
    // Padded to BLAKE2S_BLOCK_SIZE_U32_WORDS (16) boundary for aligned hashing
    let hash_buf_padded = (max_leaf_words + 15) / 16 * 16;
    let fold_buf_half = values_per_leaf / 2;

    // MW operations
    let batch_mul = MW::mul_assign_by_base(quote! { term }, quote! { base_val });
    let batch_add = MW::add_assign(quote! { dst_val }, quote! { term });
    let add_acc0 = MW::add_assign(quote! { acc0 }, quote! { term });
    let add_acc1 = MW::add_assign(quote! { acc1 }, quote! { term });
    let mul_delin = MW::mul_assign(quote! { t }, quote! { delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );
    let from_raw = MW::field_from_reduced_raw_repr(quote! { raw });
    let batch_mul_eval = MW::mul_assign(quote! { term }, quote! { eval });
    let add_claim_eval = MW::add_assign(quote! { claim }, quote! { term });

    quote! {
        #field_use_stmts
        use core::mem::MaybeUninit;
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::field_ops;
        use ::verifier_common::transcript::{Blake2sTranscript, Seed};
        use ::verifier_common::blake2s_u32::{
            AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS, BLAKE2S_BLOCK_SIZE_U32_WORDS,
        };
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::lazy_vec::LazyVec;
        use ::verifier_common::whir::{
            read_and_commit_merkle_cap, read_commit_return_merkle_cap,
            read_and_verify_pow,
            draw_query_indices, verify_merkle_path, hash_leaf_data_into_state,
        };
        use super::common::{
            verify_whir_sumcheck_step, fold_coset, materialize_gamma_powers,
            batch_claims, WhirVerificationError, read_field_el, read_field_els,
            commit_field_els, draw_field_els_into, two_inv, compute_tree_index,
        };
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
        const TOTAL_ORACLE_COLS_LOCAL: usize = #total_oracle_cols;
        const NUM_COSETS: usize = #num_cosets;
        const NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const COSET_TREE_SIZE: usize = #coset_tree_size;

        #[inline(always)]
        unsafe fn read_and_reorder_leaf<I: NonDeterminismSource>(
            hash_buf: &mut [u32],
            num_columns: usize,
        ) {
            // NDS has position-major order; reorder to column-major for hashing.
            // Unrolled over INITIAL_VALUES_PER_LEAF (== 2) positions.
            let mut col = 0;
            while col < num_columns {
                let w0 = I::read_word();
                *hash_buf.get_unchecked_mut(col * INITIAL_VALUES_PER_LEAF) = w0;
                col += 1;
            }
            col = 0;
            while col < num_columns {
                let w1 = I::read_word();
                *hash_buf.get_unchecked_mut(col * INITIAL_VALUES_PER_LEAF + 1) = w1;
                col += 1;
            }
        }

        /// Batch leaf values (column-major in hash_buf) into batched_evals.
        /// Accumulators are hoisted into locals to avoid aliasing-induced
        /// reloads/stores through the slice pointer on every iteration.
        #[inline(always)]
        unsafe fn batch_leaf_values(
            hash_buf: &[u32],
            num_columns: usize,
            gamma_powers: &[#quartic_struct],
            gamma_offset: usize,
            batched_evals: &mut [#quartic_struct],
        ) {
            // Hoist accumulators into locals — avoids reload/store through
            // batched_evals pointer every iteration (LLVM can't prove no-alias).
            let mut acc0 = *batched_evals.get_unchecked(0);
            let mut acc1 = *batched_evals.get_unchecked(1);
            let mut col = 0;
            while col < num_columns {
                let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
                // pos 0
                let raw = *hash_buf.get_unchecked(col * INITIAL_VALUES_PER_LEAF);
                let base_val = #from_raw;
                let mut term = gamma;
                #batch_mul;
                #add_acc0;
                // pos 1
                let raw = *hash_buf.get_unchecked(col * INITIAL_VALUES_PER_LEAF + 1);
                let base_val = #from_raw;
                let mut term = gamma;
                #batch_mul;
                #add_acc1;

                col += 1;
            }
            *batched_evals.get_unchecked_mut(0) = acc0;
            *batched_evals.get_unchecked_mut(1) = acc1;
        }

        #[inline(always)]
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
            batched_evals: &mut [#quartic_struct],
            query: usize,
        ) -> Result<(), WhirVerificationError> {
            let buf = hash_buf.assume_init_subarray_mut::<HASH_BUF_SIZE>();
            read_and_reorder_leaf::<I>(
                &mut buf[..leaf_words], num_columns,
            );

            // Only zero the tail of the last Blake2s block.
            // hash_leaf_data_into_state needs zero-padding within the final 16-word block.
            let block_end = leaf_words.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            if block_end > leaf_words {
                hash_buf.zero_range(leaf_words, block_end);
            }
            let buf = hash_buf.assume_init_subarray::<HASH_BUF_SIZE>();
            hash_leaf_data_into_state(hasher, buf, leaf_words);
            if !verify_merkle_path::<I>(hasher, query_index, depth, cap) {
                return Err(WhirVerificationError::MerklePathFailed { query });
            }
            batch_leaf_values(
                &buf[..leaf_words], num_columns,
                gamma_powers, gamma_offset, batched_evals,
            );
            Ok(())
        }

        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
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
                        let mut term = gamma_powers[col_idx];
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                        i += 1;
                    }
                    // Witness evals
                    i = 0;
                    while i < NUM_WIT_ORACLE_COLS {
                        let eval: #quartic_struct = read_field_el::<I>();
                        let mut term = gamma_powers[col_idx];
                        #batch_mul_eval;
                        #add_claim_eval;
                        col_idx += 1;
                        i += 1;
                    }
                    // Setup evals
                    i = 0;
                    while i < NUM_SETUP_ORACLE_COLS {
                        let eval: #quartic_struct = read_field_el::<I>();
                        let mut term = gamma_powers[col_idx];
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
                let intermediate_cap =
                    read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS>(seed);

                // --- 3. OOD: draw point, read value, commit ---
                let ood_point = {
                    let mut buf = MaybeUninit::<[#quartic_struct; 1]>::uninit();
                    draw_field_els_into(hasher, seed, &mut *buf.as_mut_ptr());
                    (*buf.as_ptr())[0]
                };

                let ood_value: #quartic_struct = read_field_el::<I>();
                commit_field_els(seed, &[ood_value]);

                // --- 4. PoW + query indices ---
                read_and_verify_pow::<I>(seed, INITIAL_POW_BITS);
                let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
                    hasher, seed, INITIAL_NUM_QUERIES, INITIAL_QUERY_INDEX_BITS,
                    INITIAL_DRAW_WORDS,
                );

                // --- 5. Delinearization challenge ---
                let delinearization_challenge = {
                    let mut buf = MaybeUninit::<[#quartic_struct; 1]>::uninit();
                    draw_field_els_into(hasher, seed, &mut *buf.as_mut_ptr());
                    (*buf.as_ptr())[0]
                };

                // --- 6. Claim correction: starts with OOD contribution ---
                let mut claim_correction = ood_value;
                #mul_ood_delin;

                // --- 7. Per-query processing ---
                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[INITIAL_RS_DOMAIN_LOG2];
                let two_inv = two_inv();
                let high_powers_offsets = [#field_one; 1 << (WHIR_FOLD_STEPS[0] - 1)];

                // Scratch buffers — fully written before read each iteration
                let mut fold_buf_a = MaybeUninit::<[#quartic_struct; FOLD_BUF_HALF]>::uninit();
                let mut fold_buf_b = MaybeUninit::<[#quartic_struct; FOLD_BUF_HALF]>::uninit();
                let mut q = 0;
                while q < INITIAL_NUM_QUERIES {
                    let query_index = *query_indices.get(q);

                    // query_index determines omega^k for the algebraic fold
                    let base_root = extended_generator.pow(query_index as u32);
                    let base_root_inv = base_root.inverse().unwrap();

                    // Tree leaves are stored sequentially by coset (with bit-reversed
                    // coset ordering).  Map from the interleaved query_index to the
                    // actual tree leaf position.
                    let tree_index = compute_tree_index(
                        query_index, NUM_COSETS, NUM_COSETS_LOG2, COSET_TREE_SIZE,
                    );

                    // batched_evals accumulates across 3 oracles — zero-init is semantic
                    let mut batched_evals = [#quartic_zero; INITIAL_VALUES_PER_LEAF];

                    // Memory oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_MEM_ORACLE_COLS, MEM_LEAF_WORDS, tree_index,
                        BASE_ORACLE_DEPTH, memory_cap, &gamma_powers[..], 0, &mut batched_evals, q,
                    )?;
                    // Witness oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_WIT_ORACLE_COLS, WIT_LEAF_WORDS, tree_index,
                        BASE_ORACLE_DEPTH, witness_cap, &gamma_powers[..], NUM_MEM_ORACLE_COLS, &mut batched_evals, q,
                    )?;
                    // Setup oracle
                    process_oracle_query::<I>(
                        hasher, hash_buf,
                        NUM_SETUP_ORACLE_COLS, SETUP_LEAF_WORDS, tree_index,
                        SETUP_ORACLE_DEPTH, setup_cap, &gamma_powers[..],
                        NUM_MEM_ORACLE_COLS + NUM_WIT_ORACLE_COLS, &mut batched_evals, q,
                    )?;

                    // Fold
                    let folded = fold_coset(
                        &batched_evals, WHIR_FOLD_STEPS[0],
                        folding_challenges.as_slice(),
                        base_root_inv, &high_powers_offsets, two_inv,
                        &mut *fold_buf_a.as_mut_ptr(), &mut *fold_buf_b.as_mut_ptr(),
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

/// Generate per-circuit WHIR verifier code for internal rounds.
pub fn generate_whir_internal_rounds<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    trace_len_log2: usize,
) -> TokenStream {
    let field_use_stmts = MW::field_use_statements();
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let field_one = MW::field_one();

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    let num_internal_rounds = num_rounds - 2; // exclude initial (0) and final (last)

    // Compute per-round constants for internal rounds (round indices 1..num_rounds-1)
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

    // Max buffer sizes for const generics
    let internal_fold_steps_range = &whir_schedule.whir_steps_schedule[1..num_rounds - 1];
    let internal_queries_range = &whir_schedule.whir_queries_schedule[1..num_rounds - 1];

    let max_internal_fold_steps = *internal_fold_steps_range.iter().max().unwrap_or(&1);
    let max_internal_values_per_leaf = 1usize << max_internal_fold_steps;
    let max_internal_leaf_ext_words = max_internal_values_per_leaf * 4; // EXT_DEGREE=4
    let internal_hash_buf_size = (max_internal_leaf_ext_words + 15) / 16 * 16;
    let max_internal_fold_buf_half = max_internal_values_per_leaf / 2;
    let max_internal_num_queries = *internal_queries_range.iter().max().unwrap_or(&1);
    let internal_draw_words_vec: Vec<usize> = internal_query_index_bits_vec
        .iter()
        .enumerate()
        .map(|(i, &bits)| {
            let nq = whir_schedule.whir_queries_schedule[i + 1];
            let total_bits = nq * bits + 32;
            ((total_bits + 255) / 256) * 8
        })
        .collect();
    let max_internal_draw_words = *internal_draw_words_vec.iter().max().unwrap_or(&8);

    let num_ir = num_internal_rounds;

    // MW operations
    let mul_delin = MW::mul_assign(quote! { t }, quote! { delinearization_challenge });
    let add_correction = MW::add_assign(quote! { claim_correction }, quote! { t });
    let add_claim = MW::add_assign(quote! { claim }, quote! { claim_correction });
    let mul_ood_delin = MW::mul_assign(
        quote! { claim_correction },
        quote! { delinearization_challenge },
    );

    quote! {
        // Additional imports for internal rounds (extending whir.rs)
        use super::common::{
            compute_high_powers_offsets, ext_from_raw_words, MAX_HIGH_POWERS, EXT_DEGREE,
        };
        use ::verifier_common::whir::read_return_merkle_cap;

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

        /// Verify one internal WHIR round (rounds 1..WHIR_ROUNDS-2).
        /// `round_idx` is 1-based (1 = first internal round).
        /// `prev_oracle_cap` is the cap committed in the previous round.
        /// Returns (new_claim, next_intermediate_cap).
        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
        pub fn verify_internal_whir_round<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            seed: &mut Seed,
            claim: #quartic_struct,
            prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
            round_idx: usize,
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
            unsafe {
                let fold_steps = WHIR_FOLD_STEPS[round_idx];
                let num_queries = WHIR_QUERIES[round_idx];
                let values_per_leaf = 1usize << fold_steps;
                let leaf_ext_words = values_per_leaf * EXT_DEGREE;
                let ir = round_idx - 1; // 0-based internal round index

                // --- 1. Sumcheck folds ---
                let mut claim = claim;
                let mut folding_challenges: LazyVec<#quartic_struct, MAX_INTERNAL_FOLD_STEPS> =
                    LazyVec::new();
                let mut round = 0;
                while round < fold_steps {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I>(
                        hasher, seed, claim, round,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    round += 1;
                }

                // --- 2. Read intermediate oracle cap (NOT committed to transcript) ---
                let intermediate_cap =
                    read_return_merkle_cap::<I, WHIR_CAP_WORDS>();

                // --- 3. OOD: draw point, read value (NOT committed to transcript) ---
                let ood_point = {
                    let mut buf = MaybeUninit::<[#quartic_struct; 1]>::uninit();
                    draw_field_els_into(hasher, seed, &mut *buf.as_mut_ptr());
                    (*buf.as_ptr())[0]
                };
                let ood_value: #quartic_struct = read_field_el::<I>();

                // --- 4. PoW + query indices ---
                read_and_verify_pow::<I>(seed, WHIR_POW_BITS[round_idx]);
                let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
                let draw_words = INTERNAL_DRAW_WORDS[ir];
                let query_indices =
                    draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
                        hasher, seed, num_queries, query_index_bits, draw_words,
                    );

                // --- 5. Delinearization challenge ---
                let delinearization_challenge = {
                    let mut buf = MaybeUninit::<[#quartic_struct; 1]>::uninit();
                    draw_field_els_into(hasher, seed, &mut *buf.as_mut_ptr());
                    (*buf.as_ptr())[0]
                };

                // --- 6. Claim correction: starts with OOD contribution ---
                let mut claim_correction = ood_value;
                #mul_ood_delin;

                // --- 7. Per-query processing ---
                let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[rs_domain_log2];
                let two_inv = two_inv();
                let num_cosets = INTERNAL_NUM_COSETS[ir];
                let num_cosets_log2 = INTERNAL_NUM_COSETS_LOG2[ir];
                let coset_tree_size = INTERNAL_COSET_TREE_SIZE[ir];
                let oracle_depth = WHIR_ORACLE_DEPTHS[round_idx - 1];

                let mut high_powers_offsets = [#field_one; MAX_HIGH_POWERS];
                compute_high_powers_offsets(fold_steps, &mut high_powers_offsets);

                // Scratch buffers
                let mut fold_buf_a =
                    MaybeUninit::<[#quartic_struct; MAX_INTERNAL_FOLD_BUF_HALF]>::uninit();
                let mut fold_buf_b =
                    MaybeUninit::<[#quartic_struct; MAX_INTERNAL_FOLD_BUF_HALF]>::uninit();
                let mut q = 0;
                while q < num_queries {
                    let query_index = *query_indices.get(q);
                    let base_root = extended_generator.pow(query_index as u32);
                    let base_root_inv = base_root.inverse().unwrap();

                    // Tree index mapping
                    let tree_index = compute_tree_index(
                        query_index, num_cosets, num_cosets_log2, coset_tree_size,
                    );

                    // Read extension field leaf values from NDS
                    let mut i = 0;
                    while i < leaf_ext_words {
                        hash_buf.write(i, I::read_word());
                        i += 1;
                    }
                    // Zero only the tail of the last Blake2s block
                    let block_end = leaf_ext_words.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
                    hash_buf.zero_range(leaf_ext_words, block_end);

                    // Hash and verify Merkle path
                    let init_buf = hash_buf.assume_init_subarray::<INTERNAL_HASH_BUF_SIZE>();
                    hash_leaf_data_into_state(hasher, init_buf, leaf_ext_words);
                    if !verify_merkle_path::<I>(
                        hasher, tree_index, oracle_depth, prev_oracle_cap,
                    ) {
                        return Err(WhirVerificationError::MerklePathFailed { query: q });
                    }

                    // Reconstruct extension field elements from buffer
                    let mut evals: LazyVec<#quartic_struct, MAX_INTERNAL_VALUES_PER_LEAF> =
                        LazyVec::new();
                    let mut j = 0;
                    while j < values_per_leaf {
                        evals.push(ext_from_raw_words(
                            &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
                        ));
                        j += 1;
                    }

                    // Fold
                    let folded = fold_coset(
                        evals.as_slice(), fold_steps,
                        folding_challenges.as_slice(),
                        base_root_inv, &high_powers_offsets[..], two_inv,
                        &mut *fold_buf_a.as_mut_ptr(), &mut *fold_buf_b.as_mut_ptr(),
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

/// Generate per-circuit WHIR verifier code for the final round.
/// The final round does sumcheck + PoW + queries but has NO OOD sample,
/// NO delinearization challenge, and NO new oracle commitment.
pub fn generate_whir_final_round<MW: MersenneWrapper>(
    whir_schedule: &WhirSchedule,
    trace_len_log2: usize,
) -> TokenStream {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let field_one = MW::field_one();

    // MW operations for monomial evaluation (Horner's method)
    let horner_mul = MW::mul_assign_by_base(quote! { eval }, quote! { query_point });
    let horner_add = MW::add_assign(quote! { eval }, quote! { coeff });

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    let final_round_idx = num_rounds - 1;
    let fold_steps = whir_schedule.whir_steps_schedule[final_round_idx];
    let num_queries = whir_schedule.whir_queries_schedule[final_round_idx];
    let values_per_leaf = 1usize << fold_steps;
    let leaf_ext_words = values_per_leaf * 4; // EXT_DEGREE=4
    let hash_buf_size = (leaf_ext_words + 15) / 16 * 16;
    let fold_buf_half = values_per_leaf / 2;

    // Compute final round geometry from the last intermediate oracle
    let mut poly_size_log2 = trace_len_log2;
    for i in 0..final_round_idx {
        poly_size_log2 -= whir_schedule.whir_steps_schedule[i];
    }
    // poly_size_log2 is the size BEFORE the final round folds
    let last_lde_factor = whir_schedule.whir_steps_lde_factors[final_round_idx - 1];
    let last_lde_factor_log2 = last_lde_factor.trailing_zeros() as usize;
    let rs_domain_log2 = poly_size_log2 + last_lde_factor_log2;
    let query_domain_log2 = rs_domain_log2 - fold_steps;
    let query_index_bits = query_domain_log2;
    let num_cosets = last_lde_factor;
    let num_cosets_log2 = last_lde_factor_log2;
    let coset_tree_size = (1usize << poly_size_log2) / values_per_leaf;
    // Oracle depth for the last intermediate oracle
    let last_oracle_depth_idx = final_round_idx - 1; // index into WHIR_ORACLE_DEPTHS

    let total_bits_needed = num_queries * query_index_bits + 32;
    let draw_words = ((total_bits_needed + 255) / 256) * 8;

    let pow_bits = whir_schedule.whir_pow_schedule[final_round_idx];
    let final_fold_power = 1u32 << fold_steps; // 2^fold_steps, used for query point computation

    quote! {
        const FINAL_FOLD_STEPS: usize = #fold_steps;
        const FINAL_NUM_QUERIES: usize = #num_queries;
        const FINAL_VALUES_PER_LEAF: usize = #values_per_leaf;
        const FINAL_LEAF_EXT_WORDS: usize = #leaf_ext_words;
        const FINAL_HASH_BUF_SIZE: usize = #hash_buf_size;
        const FINAL_FOLD_BUF_HALF: usize = #fold_buf_half;
        const FINAL_QUERY_INDEX_BITS: usize = #query_index_bits;
        const FINAL_RS_DOMAIN_LOG2: usize = #rs_domain_log2;
        const FINAL_NUM_COSETS: usize = #num_cosets;
        const FINAL_NUM_COSETS_LOG2: usize = #num_cosets_log2;
        const FINAL_COSET_TREE_SIZE: usize = #coset_tree_size;
        const FINAL_DRAW_WORDS: usize = #draw_words;
        const FINAL_POW_BITS: u32 = #pow_bits;
        const FINAL_ORACLE_DEPTH_IDX: usize = #last_oracle_depth_idx;

        /// Verify the final WHIR round.
        /// No OOD sample, no delinearization, no new oracle commitment.
        /// Queries verify against `prev_oracle_cap` (the last intermediate oracle's cap).
        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
        pub fn verify_final_whir_round<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
            seed: &mut Seed,
            claim: #quartic_struct,
            prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
        ) -> Result<(#quartic_struct, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
            unsafe {

                // --- 1. Sumcheck folds ---
                let mut claim = claim;
                let mut folding_challenges: LazyVec<#quartic_struct, FINAL_FOLD_STEPS> =
                    LazyVec::new();
                let mut round = 0;
                while round < FINAL_FOLD_STEPS {
                    let (new_claim, alpha) = verify_whir_sumcheck_step::<I>(
                        hasher, seed, claim, round,
                    )?;
                    claim = new_claim;
                    folding_challenges.push(alpha);
                    round += 1;
                }

                // --- 2. PoW + query indices ---
                // Reuse internal round const generics to share the same monomorphization
                // and avoid the compiler generating subword memory instructions (lhu/lbu)
                // that the reduced RISC-V decoder does not support.
                read_and_verify_pow::<I>(seed, FINAL_POW_BITS);
                let query_indices =
                    draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
                        hasher, seed, FINAL_NUM_QUERIES, FINAL_QUERY_INDEX_BITS, FINAL_DRAW_WORDS,
                    );

                // --- 3. Per-query processing ---
                let extended_generator = #field_struct::TWO_ADICITY_GENERATORS[FINAL_RS_DOMAIN_LOG2];
                let two_inv = two_inv();
                let oracle_depth = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];

                let mut high_powers_offsets = [#field_one; MAX_HIGH_POWERS];
                compute_high_powers_offsets(FINAL_FOLD_STEPS, &mut high_powers_offsets);

                // Scratch buffers
                let mut fold_buf_a =
                    MaybeUninit::<[#quartic_struct; FINAL_FOLD_BUF_HALF]>::uninit();
                let mut fold_buf_b =
                    MaybeUninit::<[#quartic_struct; FINAL_FOLD_BUF_HALF]>::uninit();
                // Buffers to store per-query results for fold-agreement check
                let mut folded_values: LazyVec<#quartic_struct, FINAL_NUM_QUERIES> =
                    LazyVec::new();
                let mut query_base_roots: LazyVec<#field_struct, FINAL_NUM_QUERIES> =
                    LazyVec::new();

                let mut q = 0;
                while q < FINAL_NUM_QUERIES {
                    let query_index = *query_indices.get(q);
                    let base_root = extended_generator.pow(query_index as u32);
                    let base_root_inv = base_root.inverse().unwrap();

                    // Tree index mapping
                    let tree_index = compute_tree_index(
                        query_index, FINAL_NUM_COSETS, FINAL_NUM_COSETS_LOG2, FINAL_COSET_TREE_SIZE,
                    );

                    // Read extension field leaf values from NDS
                    let mut i = 0;
                    while i < FINAL_LEAF_EXT_WORDS {
                        hash_buf.write(i, I::read_word());
                        i += 1;
                    }
                    const FINAL_BLOCK_END: usize =
                        (FINAL_LEAF_EXT_WORDS + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                        / BLAKE2S_BLOCK_SIZE_U32_WORDS * BLAKE2S_BLOCK_SIZE_U32_WORDS;
                    hash_buf.zero_range(FINAL_LEAF_EXT_WORDS, FINAL_BLOCK_END);

                    // Hash and verify Merkle path
                    let init_buf = hash_buf.assume_init_subarray::<FINAL_HASH_BUF_SIZE>();
                    hash_leaf_data_into_state(hasher, init_buf, FINAL_LEAF_EXT_WORDS);
                    if !verify_merkle_path::<I>(
                        hasher, tree_index, oracle_depth, prev_oracle_cap,
                    ) {
                        return Err(WhirVerificationError::MerklePathFailed { query: q });
                    }

                    // Reconstruct extension field elements from buffer
                    let mut evals: LazyVec<#quartic_struct, FINAL_VALUES_PER_LEAF> =
                        LazyVec::new();
                    let mut j = 0;
                    while j < FINAL_VALUES_PER_LEAF {
                        evals.push(ext_from_raw_words(
                            &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
                        ));
                        j += 1;
                    }

                    // Fold
                    let folded = fold_coset(
                        evals.as_slice(), FINAL_FOLD_STEPS,
                        folding_challenges.as_slice(),
                        base_root_inv, &high_powers_offsets[..], two_inv,
                        &mut *fold_buf_a.as_mut_ptr(), &mut *fold_buf_b.as_mut_ptr(),
                    );

                    // Store for fold-agreement check after reading monomials
                    folded_values.push(folded);
                    query_base_roots.push(base_root);

                    q += 1;
                }

                // --- 4. Read final monomials from NDS ---
                let mut monomials = [#quartic_zero; FINAL_MONOMIALS_LEN];
                read_field_els::<I>(&mut monomials);

                // --- 5. Fold-agreement check ---
                // For each query, evaluate the monomial form at the query domain
                // point and verify it matches the folded oracle value.
                let mut q = 0;
                while q < FINAL_NUM_QUERIES {
                    // query_point = base_root^(2^fold_steps) (in the query domain)
                    let query_point = query_base_roots.get(q).pow(#final_fold_power);

                    // Horner evaluation: poly(r) = c_{n-1}*r^{n-1} + ... + c_1*r + c_0
                    let mut eval = monomials[FINAL_MONOMIALS_LEN - 1];
                    let mut j = FINAL_MONOMIALS_LEN - 1;
                    while j > 0 {
                        j -= 1;
                        #horner_mul;
                        let coeff = monomials[j];
                        #horner_add;
                    }

                    if eval != *folded_values.get(q) {
                        return Err(WhirVerificationError::FoldAgreementFailed { query: q });
                    }
                    q += 1;
                }

                Ok((claim, *prev_oracle_cap))
            }
        }
    }
}

/// Generate a unified `verify_whir` function that chains initial -> internal -> final rounds.
/// Creates the hash buffer and passes it + hasher to each round.
pub fn generate_whir_verify<MW: MersenneWrapper>(whir_hash_buf_size: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();

    quote! {
        pub const WHIR_HASH_BUF_SIZE: usize = #whir_hash_buf_size;

        /// Run the full WHIR verification: initial round, all internal rounds, final round.
        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
        pub fn verify_whir<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
            batching_challenge: #quartic_struct,
            setup_cap: &[u32; SETUP_CAP_WORDS],
            memory_cap: &[u32; MEM_CAP_WORDS],
            witness_cap: &[u32; WIT_CAP_WORDS],
        ) -> Result<(), WhirVerificationError> {
            let mut hash_buf = AlignedArray64::<u32, WHIR_HASH_BUF_SIZE>::new_uninit();
            let (mut claim, mut cap) = verify_initial_whir_round::<I>(
                hasher, &mut hash_buf, seed, batching_challenge, setup_cap, memory_cap, witness_cap,
            )?;
            let mut round_idx = 1;
            while round_idx <= NUM_INTERNAL_ROUNDS {
                let (new_claim, new_cap) = verify_internal_whir_round::<I>(
                    hasher, &mut hash_buf, seed, claim, &cap, round_idx,
                )?;
                claim = new_claim;
                cap = new_cap;
                round_idx += 1;
            }
            let _ = verify_final_whir_round::<I>(hasher, &mut hash_buf, seed, claim, &cap)?;
            Ok(())
        }
    }
}

pub fn generate_whir_common<MW: MersenneWrapper>(max_fold_steps: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_zero = MW::quartic_zero();
    let quartic_one = MW::quartic_one();
    let max_high_powers = if max_fold_steps > 0 {
        1usize << (max_fold_steps - 1)
    } else {
        1
    };
    let mul_pow_gen = MW::mul_assign(quote! { pow }, quote! { set_gen_inv });
    let from_raw_words_i = MW::field_from_reduced_raw_repr(quote! { words[i] });

    let ws_add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let ws_add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let ws_add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let ws_mul_nc_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let ws_add_nc_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let ws_add_nc_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    let mul_gamma_pow = MW::mul_assign(quote! { gamma_pow }, quote! { gamma });
    let mul_term_claim = MW::mul_assign(quote! { term }, quote! { claim_i });
    let add_batched_term = MW::add_assign(quote! { batched }, quote! { term });

    let field_struct = MW::field_struct();
    let fc_sub_t_b = MW::sub_assign(quote! { t }, quote! { b });
    let fc_mul_t_challenge = MW::mul_assign(quote! { t }, quote! { challenge });
    let fc_mul_t_root = MW::mul_assign_by_base(quote! { t }, quote! { root });
    let fc_add_t_a = MW::add_assign(quote! { t }, quote! { a });
    let fc_add_t_b = MW::add_assign(quote! { t }, quote! { b });
    let fc_mul_t_two_inv = MW::mul_assign_by_base(quote! { t }, quote! { two_inv });

    quote! {
        /// Returns the multiplicative inverse of 2 in the base field.
        #[inline(always)]
        pub fn two_inv() -> #field_struct {
            #field_struct::from_u32_unchecked(2).inverse().unwrap()
        }

        /// Compute tree index from query index for Merkle path verification.
        #[inline(always)]
        pub fn compute_tree_index(
            query_index: usize,
            num_cosets: usize,
            num_cosets_log2: usize,
            coset_tree_size: usize,
        ) -> usize {
            let coset_index = query_index & (num_cosets - 1);
            let internal_index = query_index >> num_cosets_log2;
            if num_cosets == 1 {
                internal_index
            } else {
                let coset_dest = coset_index.reverse_bits()
                    >> (usize::BITS as usize - num_cosets_log2);
                coset_dest * coset_tree_size + internal_index
            }
        }

        #[derive(Clone, Debug)]
        pub enum WhirVerificationError {
            SumcheckFailed { round: usize },
            FoldAgreementFailed { query: usize },
            MerklePathFailed { query: usize },
        }

        #[inline(always)]
        pub fn verify_whir_sumcheck_step<I: NonDeterminismSource>(
            hasher: &mut DelegatedBlake2sState,
            seed: &mut Seed,
            claim: #quartic_struct,
            round: usize,
        ) -> Result<(#quartic_struct, #quartic_struct), WhirVerificationError> {
            let c0 = read_field_el::<I>();
            let c1 = read_field_el::<I>();
            let c2 = read_field_el::<I>();
            let coeffs = [c0, c1, c2];

            commit_field_els(seed, &coeffs);

            // Check: p(0) + p(1) = c0 + (c0 + c1 + c2) == claim
            let p0 = c0;
            let mut p1 = c0;
            #ws_add_p1_c1;
            #ws_add_p1_c2;
            let mut sum = p0;
            #ws_add_sum_p1;
            if sum != claim {
                return Err(WhirVerificationError::SumcheckFailed { round });
            }

            let mut challenge_buf = [#quartic_zero; 1];
            draw_field_els_into(hasher, seed, &mut challenge_buf);
            let alpha = challenge_buf[0];

            // Horner: c0 + alpha*(c1 + alpha*c2)
            let mut new_claim = c2;
            #ws_mul_nc_alpha;
            #ws_add_nc_c1;
            #ws_mul_nc_alpha;
            #ws_add_nc_c0;

            Ok((new_claim, alpha))
        }

        #[inline(always)]
        pub fn materialize_gamma_powers<const N: usize>(
            gamma: #quartic_struct,
        ) -> [#quartic_struct; N] {
            debug_assert!(N > 1);

            let mut powers: LazyVec<#quartic_struct, N> = LazyVec::new();
            powers.push(#quartic_one);
            let mut i = 1;
            let mut gamma_pow = gamma;
            while i < N - 1 {
                powers.push(gamma_pow);
                #mul_gamma_pow;
                i += 1;
            }
            powers.push(gamma_pow);

            unsafe { powers.into_array() }
        }

        #[inline(always)]
        pub fn batch_claims<const NUM_CLAIMS: usize, const CAP: usize>(
            claims: &LazyVec<#quartic_struct, CAP>,
            gamma_powers: &[#quartic_struct; NUM_CLAIMS],
        ) -> #quartic_struct {
            debug_assert!(NUM_CLAIMS > 0);
            debug_assert!(NUM_CLAIMS <= CAP);
            let mut batched = *claims.get(0);
            let mut i = 1;
            while i < NUM_CLAIMS {
                let claim_i = *claims.get(i);
                let mut term = gamma_powers[i];
                #mul_term_claim;
                #add_batched_term;
                i += 1;
            }
            batched
        }

        #[inline(always)]
        pub fn fold_coset(
            evals: &[#quartic_struct],
            num_rounds: usize,
            folding_challenges: &[#quartic_struct],
            mut root_inv: #field_struct,
            high_powers_offsets: &[#field_struct],
            two_inv: #field_struct,
            buf_a: &mut [#quartic_struct],
            buf_b: &mut [#quartic_struct],
        ) -> #quartic_struct {
            debug_assert!(num_rounds == 0 || high_powers_offsets.len() >= 1 << (num_rounds - 1));
            let mut round = 0;
            while round < num_rounds {
                let half = 1 << (num_rounds - round - 1);
                let challenge = folding_challenges[round];

                let (src, dst) = if round == 0 {
                    (evals, &mut buf_a[..half])
                } else if round % 2 == 1 {
                    (&buf_a[..half * 2], &mut buf_b[..half])
                } else {
                    (&buf_b[..half * 2], &mut buf_a[..half])
                };

                let mut pair_idx = 0;
                while pair_idx < half {
                    let a = src[pair_idx * 2];
                    let b = src[pair_idx * 2 + 1];

                    let mut t = a;
                    #fc_sub_t_b;
                    #fc_mul_t_challenge;

                    let mut root = root_inv;
                    field_ops::mul_assign(&mut root, &high_powers_offsets[pair_idx]);
                    #fc_mul_t_root;

                    #fc_add_t_a;
                    #fc_add_t_b;
                    #fc_mul_t_two_inv;

                    dst[pair_idx] = t;
                    pair_idx += 1;
                }

                field_ops::square(&mut root_inv);
                round += 1;
            }

            if num_rounds == 0 {
                evals[0]
            } else if num_rounds % 2 == 1 {
                buf_a[0]
            } else {
                buf_b[0]
            }
        }

        pub const MAX_HIGH_POWERS: usize = #max_high_powers;

        #[inline(always)]
        pub fn bitreverse_inplace<T: Copy>(arr: &mut [T]) {
            let n = arr.len();
            if n <= 1 {
                return;
            }
            let log_n = n.trailing_zeros();
            let mut i = 0;
            while i < n {
                let j = (i as u32).reverse_bits().wrapping_shr(32 - log_n) as usize;
                if i < j {
                    let tmp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = tmp;
                }
                i += 1;
            }
        }

        /// Compute bit-reversed high powers of the set-generator inverse for fold_coset.
        /// Returns the number of valid entries written (== 1 << (fold_steps - 1)).
        #[inline(always)]
        pub fn compute_high_powers_offsets(
            fold_steps: usize,
            dst: &mut [#field_struct; MAX_HIGH_POWERS],
        ) -> usize {
            let count = 1usize << (fold_steps - 1);
            let set_gen_inv = #field_struct::TWO_ADICITY_GENERATORS[fold_steps].inverse().unwrap();
            dst[0] = #field_struct::ONE;
            let mut pow = set_gen_inv;
            let mut i = 1;
            while i < count {
                dst[i] = pow;
                #mul_pow_gen;
                i += 1;
            }
            bitreverse_inplace(&mut dst[..count]);
            count
        }

        /// Reconstruct an extension field element from raw u32 words in a buffer.
        #[inline(always)]
        pub fn ext_from_raw_words(words: &[u32]) -> #quartic_struct {
            debug_assert!(words.len() >= EXT_DEGREE);
            let mut coeffs = LazyVec::<#field_struct, EXT_DEGREE>::new();
            let mut i = 0;
            while i < EXT_DEGREE {
                coeffs.push(#from_raw_words_i);
                i += 1;
            }
            unsafe { core::ptr::read(coeffs.as_slice().as_ptr().cast::<#quartic_struct>()) }
        }
    }
}
