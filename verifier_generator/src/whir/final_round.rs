use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;
use prover::gkr::prover::WhirSchedule;

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
