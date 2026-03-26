use super::common::{
    batch_claims, commit_field_els, draw_field_els_into, fold_coset, materialize_gamma_powers,
    read_field_el, read_field_els, verify_whir_sumcheck_step, WhirVerificationError,
};
use super::constants::*;
use verifier_common::blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::transcript::{Blake2sTranscript, Seed};
use verifier_common::whir::{
    draw_query_indices, hash_leaf_data_into_state, read_and_commit_merkle_cap, read_and_verify_pow,
    read_commit_return_merkle_cap, verify_merkle_path,
};
const INITIAL_VALUES_PER_LEAF: usize = 2usize;
const INITIAL_QUERY_INDEX_BITS: usize = 24usize;
const INITIAL_NUM_QUERIES: usize = 68usize;
const INITIAL_POW_BITS: u32 = 24u32;
const INITIAL_DRAW_WORDS: usize = 56usize;
const INITIAL_RS_DOMAIN_LOG2: usize = 25usize;
const MEM_LEAF_WORDS: usize = 60usize;
const WIT_LEAF_WORDS: usize = 56usize;
const SETUP_LEAF_WORDS: usize = 24usize;
const HASH_BUF_SIZE: usize = 64usize;
const FOLD_BUF_HALF: usize = 1usize;
const TOTAL_ORACLE_COLS_LOCAL: usize = 70usize;
const NUM_COSETS: usize = 2usize;
const NUM_COSETS_LOG2: usize = 1usize;
const COSET_TREE_SIZE: usize = 8388608usize;
#[inline(always)]
unsafe fn read_and_reorder_leaf<I: NonDeterminismSource>(hash_buf: &mut [u32], num_columns: usize) {
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
#[doc = r" Batch leaf values (column-major in hash_buf) into batched_evals."]
#[doc = r" Loop is col-outer so gamma_powers[col] is loaded once for both positions,"]
#[doc = r" and accumulators stay in registers across the inner (unrolled) position loop."]
#[inline(always)]
unsafe fn batch_leaf_values(
    hash_buf: &[u32],
    num_columns: usize,
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    batched_evals: &mut [BabyBearExt4],
) {
    let mut col = 0;
    while col < num_columns {
        let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
        let raw = *hash_buf.get_unchecked(col * INITIAL_VALUES_PER_LEAF);
        let base_val = BabyBearField::from_reduced_raw_repr(raw);
        let mut term = gamma;
        field_ops::mul_assign_by_base(&mut term, &base_val);
        let mut dst_val = *batched_evals.get_unchecked(0);
        field_ops::add_assign(&mut dst_val, &term);
        *batched_evals.get_unchecked_mut(0) = dst_val;
        let raw = *hash_buf.get_unchecked(col * INITIAL_VALUES_PER_LEAF + 1);
        let base_val = BabyBearField::from_reduced_raw_repr(raw);
        let mut term = gamma;
        field_ops::mul_assign_by_base(&mut term, &base_val);
        let mut dst_val = *batched_evals.get_unchecked(1);
        field_ops::add_assign(&mut dst_val, &term);
        *batched_evals.get_unchecked_mut(1) = dst_val;
        col += 1;
    }
}
#[inline(always)]
unsafe fn process_oracle_query<I: NonDeterminismSource>(
    hasher: &mut DelegatedBlake2sState,
    hash_buf: &mut AlignedArray64<u32, HASH_BUF_SIZE>,
    num_columns: usize,
    leaf_words: usize,
    query_index: usize,
    cap: &[u32],
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    batched_evals: &mut [BabyBearExt4],
) {
    read_and_reorder_leaf::<I>(&mut hash_buf[..leaf_words], num_columns);
    let padded_end = (leaf_words + 15) / 16 * 16;
    for z in leaf_words..padded_end {
        *hash_buf.get_unchecked_mut(z) = 0;
    }
    hash_leaf_data_into_state(hasher, hash_buf, leaf_words);
    assert!(verify_merkle_path::<I>(
        hasher,
        query_index,
        BASE_ORACLE_DEPTH,
        cap
    ));
    batch_leaf_values(
        &hash_buf[..leaf_words],
        num_columns,
        gamma_powers,
        gamma_offset,
        batched_evals,
    );
}
#[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
pub fn verify_initial_whir_round<I: NonDeterminismSource>(
    seed: &mut Seed,
    batching_challenge: BabyBearExt4,
    setup_cap: &[u32; WHIR_CAP_WORDS],
    memory_cap: &[u32; WHIR_CAP_WORDS],
    witness_cap: &[u32; WHIR_CAP_WORDS],
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
    unsafe {
        let mut hasher = DelegatedBlake2sState::new();
        let gamma_powers: [BabyBearExt4; TOTAL_ORACLE_COLS] =
            materialize_gamma_powers(batching_challenge);
        let mut claim = BabyBearExt4::ZERO;
        {
            let mut col_idx = 0;
            let mut i = 0;
            while i < NUM_MEM_ORACLE_COLS {
                let eval: BabyBearExt4 = read_field_el::<I>();
                let mut term = gamma_powers[col_idx];
                field_ops::mul_assign(&mut term, &eval);
                field_ops::add_assign(&mut claim, &term);
                col_idx += 1;
                i += 1;
            }
            i = 0;
            while i < NUM_WIT_ORACLE_COLS {
                let eval: BabyBearExt4 = read_field_el::<I>();
                let mut term = gamma_powers[col_idx];
                field_ops::mul_assign(&mut term, &eval);
                field_ops::add_assign(&mut claim, &term);
                col_idx += 1;
                i += 1;
            }
            i = 0;
            while i < NUM_SETUP_ORACLE_COLS {
                let eval: BabyBearExt4 = read_field_el::<I>();
                let mut term = gamma_powers[col_idx];
                field_ops::mul_assign(&mut term, &eval);
                field_ops::add_assign(&mut claim, &term);
                col_idx += 1;
                i += 1;
            }
        }
        let mut folding_challenges: LazyVec<BabyBearExt4, { WHIR_FOLD_STEPS[0] }> = LazyVec::new();
        let mut round_idx = 0;
        while round_idx < WHIR_FOLD_STEPS[0] {
            let (new_claim, alpha) =
                verify_whir_sumcheck_step::<I>(&mut hasher, seed, claim, round_idx)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round_idx += 1;
        }
        let intermediate_cap = read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS>(seed);
        let ood_point = {
            let mut buf = core::mem::MaybeUninit::<[BabyBearExt4; 1]>::uninit();
            draw_field_els_into(&mut hasher, seed, &mut *buf.as_mut_ptr());
            (*buf.as_ptr())[0]
        };
        let ood_value: BabyBearExt4 = read_field_el::<I>();
        commit_field_els(seed, &[ood_value]);
        read_and_verify_pow::<I>(seed, INITIAL_POW_BITS);
        let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
            &mut hasher,
            seed,
            INITIAL_NUM_QUERIES,
            INITIAL_QUERY_INDEX_BITS,
            INITIAL_DRAW_WORDS,
        );
        let delinearization_challenge = {
            let mut buf = core::mem::MaybeUninit::<[BabyBearExt4; 1]>::uninit();
            draw_field_els_into(&mut hasher, seed, &mut *buf.as_mut_ptr());
            (*buf.as_ptr())[0]
        };
        let mut claim_correction = ood_value;
        field_ops::mul_assign(&mut claim_correction, &delinearization_challenge);
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[INITIAL_RS_DOMAIN_LOG2];
        let two_inv = BabyBearField::from_u32_unchecked(2).inverse().unwrap();
        let high_powers_offsets = [BabyBearField::ONE; 1 << (WHIR_FOLD_STEPS[0] - 1)];
        let mut fold_buf_a = core::mem::MaybeUninit::<[BabyBearExt4; FOLD_BUF_HALF]>::uninit();
        let mut fold_buf_b = core::mem::MaybeUninit::<[BabyBearExt4; FOLD_BUF_HALF]>::uninit();
        let mut hash_buf = AlignedArray64::<u32, HASH_BUF_SIZE>::from_value(0u32);
        let mut q = 0;
        while q < INITIAL_NUM_QUERIES {
            let query_index = *query_indices.get(q);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let coset_index = query_index & (NUM_COSETS - 1);
            let internal_index = query_index / NUM_COSETS;
            let tree_index = if NUM_COSETS == 1 {
                internal_index
            } else {
                let coset_dest =
                    coset_index.reverse_bits() >> (usize::BITS as usize - NUM_COSETS_LOG2);
                coset_dest * COSET_TREE_SIZE + internal_index
            };
            let mut batched_evals = [BabyBearExt4::ZERO; INITIAL_VALUES_PER_LEAF];
            process_oracle_query::<I>(
                &mut hasher,
                &mut hash_buf,
                NUM_MEM_ORACLE_COLS,
                MEM_LEAF_WORDS,
                tree_index,
                memory_cap,
                &gamma_powers[..],
                0,
                &mut batched_evals,
            );
            process_oracle_query::<I>(
                &mut hasher,
                &mut hash_buf,
                NUM_WIT_ORACLE_COLS,
                WIT_LEAF_WORDS,
                tree_index,
                witness_cap,
                &gamma_powers[..],
                NUM_MEM_ORACLE_COLS,
                &mut batched_evals,
            );
            process_oracle_query::<I>(
                &mut hasher,
                &mut hash_buf,
                NUM_SETUP_ORACLE_COLS,
                SETUP_LEAF_WORDS,
                tree_index,
                setup_cap,
                &gamma_powers[..],
                NUM_MEM_ORACLE_COLS + NUM_WIT_ORACLE_COLS,
                &mut batched_evals,
            );
            let folded = fold_coset(
                &batched_evals,
                WHIR_FOLD_STEPS[0],
                folding_challenges.as_slice(),
                base_root_inv,
                &high_powers_offsets,
                two_inv,
                &mut *fold_buf_a.as_mut_ptr(),
                &mut *fold_buf_b.as_mut_ptr(),
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
use super::common::{compute_high_powers_offsets, ext_from_raw_words, EXT_DEGREE, MAX_HIGH_POWERS};
use verifier_common::whir::read_return_merkle_cap;
pub const NUM_INTERNAL_ROUNDS: usize = 4usize;
const INTERNAL_QUERY_INDEX_BITS: [usize; NUM_INTERNAL_ROUNDS] =
    [22usize, 21usize, 18usize, 14usize];
const INTERNAL_NUM_COSETS: [usize; NUM_INTERNAL_ROUNDS] = [8usize, 64usize, 128usize, 128usize];
const INTERNAL_NUM_COSETS_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [3usize, 6usize, 7usize, 7usize];
const INTERNAL_COSET_TREE_SIZE: [usize; NUM_INTERNAL_ROUNDS] =
    [524288usize, 32768usize, 2048usize, 128usize];
const INTERNAL_RS_DOMAIN_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [26usize, 25usize, 22usize, 18usize];
const MAX_INTERNAL_FOLD_STEPS: usize = 4usize;
const MAX_INTERNAL_VALUES_PER_LEAF: usize = 16usize;
const INTERNAL_HASH_BUF_SIZE: usize = 64usize;
const MAX_INTERNAL_FOLD_BUF_HALF: usize = 8usize;
const MAX_INTERNAL_NUM_QUERIES: usize = 23usize;
const MAX_INTERNAL_DRAW_WORDS: usize = 24usize;
const INTERNAL_DRAW_WORDS: [usize; NUM_INTERNAL_ROUNDS] = [24usize, 16usize, 8usize, 8usize];
#[doc = r" Verify one internal WHIR round (rounds 1..WHIR_ROUNDS-2)."]
#[doc = r" `round_idx` is 1-based (1 = first internal round)."]
#[doc = r" `prev_oracle_cap` is the cap committed in the previous round."]
#[doc = r" Returns (new_claim, next_intermediate_cap)."]
#[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
pub fn verify_internal_whir_round<I: NonDeterminismSource>(
    seed: &mut Seed,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
    round_idx: usize,
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
    unsafe {
        let mut hasher = DelegatedBlake2sState::new();
        let fold_steps = WHIR_FOLD_STEPS[round_idx];
        let num_queries = WHIR_QUERIES[round_idx];
        let values_per_leaf = 1usize << fold_steps;
        let leaf_ext_words = values_per_leaf * EXT_DEGREE;
        let ir = round_idx - 1;
        let mut claim = claim;
        let mut folding_challenges: LazyVec<BabyBearExt4, MAX_INTERNAL_FOLD_STEPS> = LazyVec::new();
        let mut round = 0;
        while round < fold_steps {
            let (new_claim, alpha) =
                verify_whir_sumcheck_step::<I>(&mut hasher, seed, claim, round)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round += 1;
        }
        let intermediate_cap = read_return_merkle_cap::<I, WHIR_CAP_WORDS>();
        let ood_point = {
            let mut buf = core::mem::MaybeUninit::<[BabyBearExt4; 1]>::uninit();
            draw_field_els_into(&mut hasher, seed, &mut *buf.as_mut_ptr());
            (*buf.as_ptr())[0]
        };
        let ood_value: BabyBearExt4 = read_field_el::<I>();
        read_and_verify_pow::<I>(seed, WHIR_POW_BITS[round_idx]);
        let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
        let draw_words = INTERNAL_DRAW_WORDS[ir];
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            &mut hasher,
            seed,
            num_queries,
            query_index_bits,
            draw_words,
        );
        let delinearization_challenge = {
            let mut buf = core::mem::MaybeUninit::<[BabyBearExt4; 1]>::uninit();
            draw_field_els_into(&mut hasher, seed, &mut *buf.as_mut_ptr());
            (*buf.as_ptr())[0]
        };
        let mut claim_correction = ood_value;
        field_ops::mul_assign(&mut claim_correction, &delinearization_challenge);
        let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[rs_domain_log2];
        let two_inv = BabyBearField::from_u32_unchecked(2).inverse().unwrap();
        let num_cosets = INTERNAL_NUM_COSETS[ir];
        let num_cosets_log2 = INTERNAL_NUM_COSETS_LOG2[ir];
        let coset_tree_size = INTERNAL_COSET_TREE_SIZE[ir];
        let oracle_depth = WHIR_ORACLE_DEPTHS[round_idx - 1];
        let mut high_powers_offsets = [BabyBearField::ONE; MAX_HIGH_POWERS];
        compute_high_powers_offsets(fold_steps, &mut high_powers_offsets);
        let mut fold_buf_a =
            core::mem::MaybeUninit::<[BabyBearExt4; MAX_INTERNAL_FOLD_BUF_HALF]>::uninit();
        let mut fold_buf_b =
            core::mem::MaybeUninit::<[BabyBearExt4; MAX_INTERNAL_FOLD_BUF_HALF]>::uninit();
        let mut hash_buf = AlignedArray64::<u32, INTERNAL_HASH_BUF_SIZE>::from_value(0u32);
        let mut q = 0;
        while q < num_queries {
            let query_index = *query_indices.get(q);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let coset_index = query_index & (num_cosets - 1);
            let internal_index = query_index / num_cosets;
            let tree_index = if num_cosets == 1 {
                internal_index
            } else {
                let coset_dest =
                    coset_index.reverse_bits() >> (usize::BITS as usize - num_cosets_log2);
                coset_dest * coset_tree_size + internal_index
            };
            let mut i = 0;
            while i < leaf_ext_words {
                *hash_buf.get_unchecked_mut(i) = I::read_word();
                i += 1;
            }
            while i < INTERNAL_HASH_BUF_SIZE {
                *hash_buf.get_unchecked_mut(i) = 0;
                i += 1;
            }
            hash_leaf_data_into_state(&mut hasher, &hash_buf, leaf_ext_words);
            assert!(verify_merkle_path::<I>(
                &mut hasher,
                tree_index,
                oracle_depth,
                prev_oracle_cap,
            ));
            let mut evals = [BabyBearExt4::ZERO; MAX_INTERNAL_VALUES_PER_LEAF];
            let mut j = 0;
            while j < values_per_leaf {
                evals[j] = ext_from_raw_words(&hash_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE]);
                j += 1;
            }
            let folded = fold_coset(
                &evals[..values_per_leaf],
                fold_steps,
                folding_challenges.as_slice(),
                base_root_inv,
                &high_powers_offsets[..],
                two_inv,
                &mut *fold_buf_a.as_mut_ptr(),
                &mut *fold_buf_b.as_mut_ptr(),
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
const FINAL_LEAF_EXT_WORDS: usize = 64usize;
const FINAL_HASH_BUF_SIZE: usize = 64usize;
const FINAL_FOLD_BUF_HALF: usize = 8usize;
const FINAL_QUERY_INDEX_BITS: usize = 10usize;
const FINAL_RS_DOMAIN_LOG2: usize = 14usize;
const FINAL_NUM_COSETS: usize = 128usize;
const FINAL_NUM_COSETS_LOG2: usize = 7usize;
const FINAL_COSET_TREE_SIZE: usize = 8usize;
const FINAL_DRAW_WORDS: usize = 8usize;
const FINAL_POW_BITS: u32 = 24u32;
const FINAL_ORACLE_DEPTH_IDX: usize = 4usize;
#[doc = r" Verify the final WHIR round."]
#[doc = r" No OOD sample, no delinearization, no new oracle commitment."]
#[doc = r" Queries verify against `prev_oracle_cap` (the last intermediate oracle's cap)."]
#[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
pub fn verify_final_whir_round<I: NonDeterminismSource>(
    seed: &mut Seed,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), WhirVerificationError> {
    unsafe {
        let mut hasher = DelegatedBlake2sState::new();
        let mut claim = claim;
        let mut folding_challenges: LazyVec<BabyBearExt4, FINAL_FOLD_STEPS> = LazyVec::new();
        let mut round = 0;
        while round < FINAL_FOLD_STEPS {
            let (new_claim, alpha) =
                verify_whir_sumcheck_step::<I>(&mut hasher, seed, claim, round)?;
            claim = new_claim;
            folding_challenges.push(alpha);
            round += 1;
        }
        read_and_verify_pow::<I>(seed, FINAL_POW_BITS);
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            &mut hasher,
            seed,
            FINAL_NUM_QUERIES,
            FINAL_QUERY_INDEX_BITS,
            FINAL_DRAW_WORDS,
        );
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[FINAL_RS_DOMAIN_LOG2];
        let two_inv = BabyBearField::from_u32_unchecked(2).inverse().unwrap();
        let oracle_depth = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];
        let mut high_powers_offsets = [BabyBearField::ONE; MAX_HIGH_POWERS];
        compute_high_powers_offsets(FINAL_FOLD_STEPS, &mut high_powers_offsets);
        let mut fold_buf_a =
            core::mem::MaybeUninit::<[BabyBearExt4; FINAL_FOLD_BUF_HALF]>::uninit();
        let mut fold_buf_b =
            core::mem::MaybeUninit::<[BabyBearExt4; FINAL_FOLD_BUF_HALF]>::uninit();
        let mut hash_buf = AlignedArray64::<u32, FINAL_HASH_BUF_SIZE>::from_value(0u32);
        let mut folded_values: [BabyBearExt4; FINAL_NUM_QUERIES] =
            [BabyBearExt4::ZERO; FINAL_NUM_QUERIES];
        let mut query_base_roots: [BabyBearField; FINAL_NUM_QUERIES] =
            [BabyBearField::ONE; FINAL_NUM_QUERIES];
        let mut q = 0;
        while q < FINAL_NUM_QUERIES {
            let query_index = *query_indices.get(q);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let coset_index = query_index & (FINAL_NUM_COSETS - 1);
            let internal_index = query_index / FINAL_NUM_COSETS;
            let tree_index = if FINAL_NUM_COSETS == 1 {
                internal_index
            } else {
                let coset_dest =
                    coset_index.reverse_bits() >> (usize::BITS as usize - FINAL_NUM_COSETS_LOG2);
                coset_dest * FINAL_COSET_TREE_SIZE + internal_index
            };
            let mut i = 0;
            while i < FINAL_LEAF_EXT_WORDS {
                *hash_buf.get_unchecked_mut(i) = I::read_word();
                i += 1;
            }
            while i < FINAL_HASH_BUF_SIZE {
                *hash_buf.get_unchecked_mut(i) = 0;
                i += 1;
            }
            hash_leaf_data_into_state(&mut hasher, &hash_buf, FINAL_LEAF_EXT_WORDS);
            assert!(verify_merkle_path::<I>(
                &mut hasher,
                tree_index,
                oracle_depth,
                prev_oracle_cap,
            ));
            let mut evals = [BabyBearExt4::ZERO; FINAL_VALUES_PER_LEAF];
            let mut j = 0;
            while j < FINAL_VALUES_PER_LEAF {
                evals[j] = ext_from_raw_words(&hash_buf[j * EXT_DEGREE..(j + 1) * EXT_DEGREE]);
                j += 1;
            }
            let folded = fold_coset(
                &evals[..],
                FINAL_FOLD_STEPS,
                folding_challenges.as_slice(),
                base_root_inv,
                &high_powers_offsets[..],
                two_inv,
                &mut *fold_buf_a.as_mut_ptr(),
                &mut *fold_buf_b.as_mut_ptr(),
            );
            *folded_values.get_unchecked_mut(q) = folded;
            *query_base_roots.get_unchecked_mut(q) = base_root;
            q += 1;
        }
        let mut monomials = [BabyBearExt4::ZERO; FINAL_MONOMIALS_LEN];
        read_field_els::<I>(&mut monomials);
        let mut q = 0;
        while q < FINAL_NUM_QUERIES {
            let query_point = query_base_roots[q].pow(16u32);
            let mut eval = monomials[FINAL_MONOMIALS_LEN - 1];
            let mut j = FINAL_MONOMIALS_LEN - 1;
            while j > 0 {
                j -= 1;
                field_ops::mul_assign_by_base(&mut eval, &query_point);
                let coeff = monomials[j];
                field_ops::add_assign(&mut eval, &coeff);
            }
            assert!(eval == folded_values[q]);
            q += 1;
        }
        Ok((claim, *prev_oracle_cap))
    }
}
