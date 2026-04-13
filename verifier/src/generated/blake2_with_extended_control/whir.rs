use super::common::{
    compute_tree_index, draw_single_field_el, fold_coset, materialize_gamma_powers,
    process_oracle_query, read_field_el, read_field_els, read_reduced_field_el,
    verify_whir_sumcheck_step,
};
use super::constants::*;
use core::mem::MaybeUninit;
use verifier_common::blake2s_u32::{
    AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::Field;
use verifier_common::field_ops;
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::whir::{
    draw_query_indices, read_and_verify_pow, read_commit_return_merkle_cap,
};
const INITIAL_VALUES_PER_LEAF: usize = 2usize;
const INITIAL_QUERY_INDEX_BITS: usize = 20usize;
const INITIAL_NUM_QUERIES: usize = 68usize;
const INITIAL_POW_BITS: u32 = 24u32;
const INITIAL_DRAW_WORDS: usize = 48usize;
const INITIAL_RS_DOMAIN_LOG2: usize = 21usize;
const HASH_BUF_SIZE: usize = 1296usize;
const FOLD_BUF_HALF: usize = 1usize;
const NUM_COSETS: usize = 2usize;
const NUM_COSETS_LOG2: usize = 1usize;
const COSET_TREE_SIZE: usize = 524288usize;
pub fn verify_initial_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    batching_challenge: BabyBearExt4,
    oracle_caps: &[u32; TOTAL_CAP_WORDS],
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), E::Error> {
    unsafe {
        let gamma_powers: [BabyBearExt4; TOTAL_ORACLE_COLS] =
            materialize_gamma_powers(batching_challenge);
        let mut claim = BabyBearExt4::ZERO;
        {
            let mut col_idx = 0;
            let mut oracle_idx = 0;
            while oracle_idx < NUM_ORACLES {
                let num_cols = ORACLE_NUM_COLS[oracle_idx];
                let mut i = 0;
                while i < num_cols {
                    let eval: BabyBearExt4 = read_field_el::<I>();
                    let mut term = unsafe { *gamma_powers.get_unchecked(col_idx) };
                    field_ops::mul_assign(&mut term, &eval);
                    field_ops::add_assign(&mut claim, &term);
                    col_idx += 1;
                    i += 1;
                }
                oracle_idx += 1;
            }
        }
        let mut folding_challenges: LazyVec<BabyBearExt4, { WHIR_FOLD_STEPS[0] }> = LazyVec::new();
        let mut round_idx = 0;
        while round_idx < WHIR_FOLD_STEPS[0] {
            let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(ts, claim, round_idx)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round_idx += 1;
        }
        const CAP_COMMIT_BUF: usize = {
            let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_CAP_WORDS;
            (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
                * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        let intermediate_cap =
            read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(ts);
        let _ood_point = draw_single_field_el(ts);
        const OOD_DATA_WORDS: usize = super::common::EXT_DEGREE;
        const OOD_COMMIT_BUF: usize = {
            let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + OOD_DATA_WORDS;
            (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
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
        let ood_value: BabyBearExt4 = unsafe { *ood_buf.data_as::<BabyBearExt4>(1).as_ptr() };
        ts.commit(&mut ood_buf, OOD_DATA_WORDS);
        read_and_verify_pow::<I>(ts, INITIAL_POW_BITS);
        let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
            ts,
            INITIAL_NUM_QUERIES,
            INITIAL_QUERY_INDEX_BITS,
            INITIAL_DRAW_WORDS,
        );
        let delinearization_challenge = draw_single_field_el(ts);
        let mut claim_correction = ood_value;
        field_ops::mul_assign(&mut claim_correction, &delinearization_challenge);
        let extended_generator_inv =
            BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[INITIAL_RS_DOMAIN_LOG2];
        let mut high_powers_offsets = LazyVec::<BabyBearField, MAX_HIGH_POWERS>::new();
        compute_high_powers_offsets(WHIR_FOLD_STEPS[0], &mut high_powers_offsets);
        let mut fold_buf_a = LazyVec::<BabyBearExt4, FOLD_BUF_HALF>::new();
        fold_buf_a.set_len(FOLD_BUF_HALF);
        let mut fold_buf_b = LazyVec::<BabyBearExt4, FOLD_BUF_HALF>::new();
        fold_buf_b.set_len(FOLD_BUF_HALF);
        let mut q = 0;
        while q < INITIAL_NUM_QUERIES {
            let query_index = *query_indices.get(q);
            let base_root_inv = extended_generator_inv.pow(query_index as u32);
            let tree_index =
                compute_tree_index(query_index, NUM_COSETS, NUM_COSETS_LOG2, COSET_TREE_SIZE);
            let mut acc0 = BabyBearExt4::ZERO;
            let mut acc1 = BabyBearExt4::ZERO;
            process_oracle_query::<I, E, WHIR_HASH_BUF_SIZE, 450usize>(
                &mut ts.hasher,
                hash_buf,
                225usize,
                tree_index,
                ORACLE_DEPTHS[0usize],
                &oracle_caps[0usize..0usize + ORACLE_CAP_WORDS[0usize]],
                &gamma_powers[..],
                0usize,
                &mut acc0,
                &mut acc1,
                q,
            )?;
            process_oracle_query::<I, E, WHIR_HASH_BUF_SIZE, 1292usize>(
                &mut ts.hasher,
                hash_buf,
                646usize,
                tree_index,
                ORACLE_DEPTHS[1usize],
                &oracle_caps[128usize..128usize + ORACLE_CAP_WORDS[1usize]],
                &gamma_powers[..],
                225usize,
                &mut acc0,
                &mut acc1,
                q,
            )?;
            process_oracle_query::<I, E, WHIR_HASH_BUF_SIZE, 8usize>(
                &mut ts.hasher,
                hash_buf,
                4usize,
                tree_index,
                ORACLE_DEPTHS[2usize],
                &oracle_caps[256usize..256usize + ORACLE_CAP_WORDS[2usize]],
                &gamma_powers[..],
                871usize,
                &mut acc0,
                &mut acc1,
                q,
            )?;
            let batched_evals = [acc0, acc1];
            let folded = fold_coset(
                &batched_evals,
                WHIR_FOLD_STEPS[0],
                folding_challenges.as_slice(),
                base_root_inv,
                unsafe { high_powers_offsets.as_array::<{ 1 << (WHIR_FOLD_STEPS[0] - 1) }>() },
                fold_buf_a.as_mut_slice(),
                fold_buf_b.as_mut_slice(),
            );
            let mut t = folded;
            field_ops::mul_assign(&mut t, &delinearization_challenge);
            field_ops::add_assign(&mut claim_correction, &t);
            q += 1;
        }
        field_ops::add_assign(&mut claim, &claim_correction);
        Ok((claim, intermediate_cap))
    }
}
use super::common::{
    compute_high_powers_offsets, ext_from_raw_word_slice, EXT_DEGREE, MAX_HIGH_POWERS,
};
use verifier_common::whir::{
    hash_leaf_data_into_state, read_return_merkle_cap, verify_merkle_path,
};
pub const NUM_INTERNAL_ROUNDS: usize = 3usize;
const INTERNAL_QUERY_INDEX_BITS: [usize; NUM_INTERNAL_ROUNDS] = [18usize, 17usize, 14usize];
const INTERNAL_NUM_COSETS: [usize; NUM_INTERNAL_ROUNDS] = [8usize, 64usize, 128usize];
const INTERNAL_NUM_COSETS_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [3usize, 6usize, 7usize];
const INTERNAL_COSET_TREE_SIZE: [usize; NUM_INTERNAL_ROUNDS] = [32768usize, 2048usize, 128usize];
const INTERNAL_RS_DOMAIN_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [22usize, 21usize, 18usize];
const MAX_INTERNAL_FOLD_STEPS: usize = 4usize;
const MAX_INTERNAL_VALUES_PER_LEAF: usize = 16usize;
const MAX_INTERNAL_LEAF_EXT_WORDS: usize = MAX_INTERNAL_VALUES_PER_LEAF * EXT_DEGREE;
const INTERNAL_HASH_BUF_SIZE: usize = MAX_INTERNAL_LEAF_EXT_WORDS
    .div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS)
    * BLAKE2S_BLOCK_SIZE_U32_WORDS;
const MAX_INTERNAL_FOLD_BUF_HALF: usize = 8usize;
const MAX_INTERNAL_NUM_QUERIES: usize = 23usize;
const MAX_INTERNAL_DRAW_WORDS: usize = 16usize;
const INTERNAL_DRAW_WORDS: [usize; NUM_INTERNAL_ROUNDS] = [16usize, 8usize, 8usize];
pub fn verify_internal_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
    round_idx: usize,
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), E::Error> {
    unsafe {
        let fold_steps = WHIR_FOLD_STEPS[round_idx];
        let num_queries = WHIR_QUERIES[round_idx];
        let values_per_leaf = 1usize << fold_steps;
        let leaf_ext_words = values_per_leaf * EXT_DEGREE;
        let ir = round_idx - 1;
        let mut claim = claim;
        let mut folding_challenges: LazyVec<BabyBearExt4, MAX_INTERNAL_FOLD_STEPS> = LazyVec::new();
        let mut round = 0;
        while round < fold_steps {
            let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(ts, claim, round)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round += 1;
        }
        let intermediate_cap = read_return_merkle_cap::<I, WHIR_CAP_WORDS>();
        let _ood_point = draw_single_field_el(ts);
        let ood_value: BabyBearExt4 = read_field_el::<I>();
        read_and_verify_pow::<I>(ts, WHIR_POW_BITS[round_idx]);
        let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
        let draw_words = INTERNAL_DRAW_WORDS[ir];
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            ts,
            num_queries,
            query_index_bits,
            draw_words,
        );
        let delinearization_challenge = draw_single_field_el(ts);
        let mut claim_correction = ood_value;
        field_ops::mul_assign(&mut claim_correction, &delinearization_challenge);
        let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
        let extended_generator_inv = BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[rs_domain_log2];
        let num_cosets = INTERNAL_NUM_COSETS[ir];
        let num_cosets_log2 = INTERNAL_NUM_COSETS_LOG2[ir];
        let coset_tree_size = INTERNAL_COSET_TREE_SIZE[ir];
        let oracle_depth = WHIR_ORACLE_DEPTHS[round_idx - 1];
        let mut high_powers_offsets = LazyVec::<BabyBearField, MAX_HIGH_POWERS>::new();
        compute_high_powers_offsets(fold_steps, &mut high_powers_offsets);
        let mut fold_buf_a = LazyVec::<BabyBearExt4, MAX_INTERNAL_FOLD_BUF_HALF>::new();
        fold_buf_a.set_len(MAX_INTERNAL_FOLD_BUF_HALF);
        let mut fold_buf_b = LazyVec::<BabyBearExt4, MAX_INTERNAL_FOLD_BUF_HALF>::new();
        fold_buf_b.set_len(MAX_INTERNAL_FOLD_BUF_HALF);
        let mut q = 0;
        while q < num_queries {
            let query_index = *query_indices.get(q);
            let base_root_inv = extended_generator_inv.pow(query_index as u32);
            let tree_index =
                compute_tree_index(query_index, num_cosets, num_cosets_log2, coset_tree_size);
            {
                let mut i = 0;
                while i < leaf_ext_words {
                    hash_buf.write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            let block_end = (leaf_ext_words).next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            hash_buf.zero_range(leaf_ext_words, block_end);
            let init_buf = hash_buf.assume_init_subarray::<INTERNAL_HASH_BUF_SIZE>();
            hash_leaf_data_into_state(&mut ts.hasher, init_buf, leaf_ext_words);
            if !verify_merkle_path::<I>(&mut ts.hasher, tree_index, oracle_depth, prev_oracle_cap) {
                return Err(E::whir_merkle_path_failed(q));
            }
            let mut evals: LazyVec<BabyBearExt4, { MAX_INTERNAL_VALUES_PER_LEAF }> = LazyVec::new();
            let mut j = 0;
            while j < MAX_INTERNAL_VALUES_PER_LEAF {
                evals.push(ext_from_raw_word_slice(
                    &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
                ));
                j += 1;
            }
            let folded = fold_coset(
                evals.as_slice(),
                fold_steps,
                folding_challenges.as_slice(),
                base_root_inv,
                high_powers_offsets.as_slice(),
                fold_buf_a.as_mut_slice(),
                fold_buf_b.as_mut_slice(),
            );
            let mut t = folded;
            field_ops::mul_assign(&mut t, &delinearization_challenge);
            field_ops::add_assign(&mut claim_correction, &t);
            q += 1;
        }
        field_ops::add_assign(&mut claim, &claim_correction);
        Ok((claim, intermediate_cap))
    }
}
const FINAL_FOLD_STEPS: usize = 4usize;
const FINAL_NUM_QUERIES: usize = 10usize;
const FINAL_VALUES_PER_LEAF: usize = 16usize;
const FINAL_LEAF_EXT_WORDS: usize = FINAL_VALUES_PER_LEAF * EXT_DEGREE;
const FINAL_HASH_BUF_SIZE: usize =
    FINAL_LEAF_EXT_WORDS.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS;
const FINAL_FOLD_BUF_HALF: usize = 8usize;
const FINAL_QUERY_INDEX_BITS: usize = 10usize;
const FINAL_RS_DOMAIN_LOG2: usize = 14usize;
const FINAL_NUM_COSETS: usize = 128usize;
const FINAL_NUM_COSETS_LOG2: usize = 7usize;
const FINAL_COSET_TREE_SIZE: usize = 8usize;
const FINAL_DRAW_WORDS: usize = 8usize;
const FINAL_POW_BITS: u32 = 24u32;
const FINAL_ORACLE_DEPTH_IDX: usize = 3usize;
pub fn verify_final_whir_round<I: NonDeterminismSource, E: ErrorCreator>(
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
) -> Result<(), E::Error> {
    unsafe {
        let mut claim = claim;
        let mut folding_challenges: LazyVec<BabyBearExt4, FINAL_FOLD_STEPS> = LazyVec::new();
        let mut round = 0;
        while round < FINAL_FOLD_STEPS {
            let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(ts, claim, round)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round += 1;
        }
        read_and_verify_pow::<I>(ts, FINAL_POW_BITS);
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            ts,
            FINAL_NUM_QUERIES,
            FINAL_QUERY_INDEX_BITS,
            FINAL_DRAW_WORDS,
        );
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[FINAL_RS_DOMAIN_LOG2];
        let extended_generator_inv =
            BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[FINAL_RS_DOMAIN_LOG2];
        let oracle_depth = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];
        let mut high_powers_offsets = LazyVec::<BabyBearField, MAX_HIGH_POWERS>::new();
        compute_high_powers_offsets(FINAL_FOLD_STEPS, &mut high_powers_offsets);
        let mut fold_buf_a = LazyVec::<BabyBearExt4, FINAL_FOLD_BUF_HALF>::new();
        fold_buf_a.set_len(FINAL_FOLD_BUF_HALF);
        let mut fold_buf_b = LazyVec::<BabyBearExt4, FINAL_FOLD_BUF_HALF>::new();
        fold_buf_b.set_len(FINAL_FOLD_BUF_HALF);
        let mut folded_values: LazyVec<BabyBearExt4, FINAL_NUM_QUERIES> = LazyVec::new();
        let mut query_base_roots: LazyVec<BabyBearField, FINAL_NUM_QUERIES> = LazyVec::new();
        let mut q = 0;
        while q < FINAL_NUM_QUERIES {
            let query_index = *query_indices.get(q);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = extended_generator_inv.pow(query_index as u32);
            let tree_index = compute_tree_index(
                query_index,
                FINAL_NUM_COSETS,
                FINAL_NUM_COSETS_LOG2,
                FINAL_COSET_TREE_SIZE,
            );
            {
                let mut i = 0;
                while i < FINAL_LEAF_EXT_WORDS {
                    hash_buf.write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            let block_end = (FINAL_LEAF_EXT_WORDS).next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            hash_buf.zero_range(FINAL_LEAF_EXT_WORDS, block_end);
            let init_buf = hash_buf.assume_init_subarray::<FINAL_HASH_BUF_SIZE>();
            hash_leaf_data_into_state(&mut ts.hasher, init_buf, FINAL_LEAF_EXT_WORDS);
            if !verify_merkle_path::<I>(&mut ts.hasher, tree_index, oracle_depth, prev_oracle_cap) {
                return Err(E::whir_merkle_path_failed(q));
            }
            let mut evals: LazyVec<BabyBearExt4, { FINAL_VALUES_PER_LEAF }> = LazyVec::new();
            let mut j = 0;
            while j < FINAL_VALUES_PER_LEAF {
                evals.push(ext_from_raw_word_slice(
                    &init_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE],
                ));
                j += 1;
            }
            let folded = fold_coset(
                evals.as_slice(),
                FINAL_FOLD_STEPS,
                folding_challenges.as_slice(),
                base_root_inv,
                high_powers_offsets.as_slice(),
                fold_buf_a.as_mut_slice(),
                fold_buf_b.as_mut_slice(),
            );
            folded_values.push(folded);
            query_base_roots.push(base_root);
            q += 1;
        }
        let mut monomials = LazyVec::<BabyBearExt4, FINAL_MONOMIALS_LEN>::new();
        monomials.set_len(FINAL_MONOMIALS_LEN);
        read_field_els::<I>(monomials.as_mut_slice());
        let mut q = 0;
        while q < FINAL_NUM_QUERIES {
            let mut query_point = *query_base_roots.get(q);
            query_point.exp_power_of_2(FINAL_FOLD_STEPS);
            let mut eval = *monomials.get_unchecked(FINAL_MONOMIALS_LEN - 1);
            let mut j = FINAL_MONOMIALS_LEN - 1;
            while j > 0 {
                j -= 1;
                field_ops::mul_assign_by_base(&mut eval, &query_point);
                let coeff = *monomials.get_unchecked(j);
                field_ops::add_assign(&mut eval, &coeff);
            }
            if eval != *folded_values.get(q) {
                return Err(E::whir_fold_agreement_failed(q));
            }
            q += 1;
        }
        Ok(())
    }
}
pub const WHIR_HASH_BUF_SIZE: usize = 1296usize;
pub fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
    ts: &mut TranscriptState,
    batching_challenge: BabyBearExt4,
    oracle_caps: &[u32; TOTAL_CAP_WORDS],
) -> Result<(), E::Error> {
    let mut hash_buf = AlignedArray64::<u32, WHIR_HASH_BUF_SIZE>::new_uninit();
    let (mut claim, mut cap) =
        verify_initial_whir_round::<I, E>(ts, &mut hash_buf, batching_challenge, oracle_caps)?;
    let mut round_idx = 1;
    while round_idx <= NUM_INTERNAL_ROUNDS {
        let (new_claim, new_cap) =
            verify_internal_whir_round::<I, E>(ts, &mut hash_buf, claim, &cap, round_idx)?;
        claim = new_claim;
        cap = new_cap;
        round_idx += 1;
    }
    verify_final_whir_round::<I, E>(ts, &mut hash_buf, claim, &cap)?;
    Ok(())
}
