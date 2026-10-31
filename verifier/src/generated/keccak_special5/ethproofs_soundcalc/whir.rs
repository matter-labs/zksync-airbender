#![allow(
    dead_code,
    unused_imports,
    unused_unsafe,
    unused_assignments,
    clippy::needless_range_loop,
    clippy::too_many_arguments,
    clippy::manual_div_ceil,
    clippy::borrow_deref_ref,
    clippy::identity_op,
    clippy::missing_safety_doc,
    clippy::duplicate_mod,
    clippy::large_const_arrays
)]
#[allow(unused_imports)]
use super::common::{
    compute_tree_index, draw_fresh_single_field_el, eval_multilinear_with_monomial_tensor,
    fold_whir_accumulator, materialize_gamma_powers, precompute_monomial_tensor,
    process_oracle_query, process_oracle_query_multiproof, push_whir_base_pow_entry,
    push_whir_pow_entry, read_reduced_field_el, verify_whir_sumcheck_step,
};
use super::constants::*;
use core::mem::MaybeUninit;
use verifier_common::blake2s_u32::{
    AlignedArray64, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
#[allow(unused_imports)]
use verifier_common::whir::multiproof::{
    sort_queries_by_tree_index, verify_merkle_multiproof_leaf, MerkleMultiproofStack, NO_NEXT_INDEX,
};
use verifier_common::whir::{
    draw_query_indices, read_and_verify_pow, read_commit_return_merkle_cap,
};
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn process_oracle_query_single_value<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const BUF_SIZE: usize,
    const LEAF_WORDS: usize,
>(
    hasher: &mut ::verifier_common::blake2s_u32::DelegatedBlake2sState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, BUF_SIZE>,
    num_columns: usize,
    query_index: usize,
    depth: usize,
    cap: &[u32],
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    acc: &mut BabyBearExt4,
    query: usize,
    nd_source: &mut I,
) -> Result<(), E::Error> {
    use verifier_common::whir::{hash_leaf_data_into_state, verify_merkle_path};
    let buf = hash_buf.assume_init_subarray_mut::<BUF_SIZE>();
    let mut col = 0;
    while col < num_columns {
        let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
        let raw = read_reduced_field_el::<I>(nd_source);
        *buf.get_unchecked_mut(col) = raw.as_u32_raw_repr();
        let base_val = raw;
        field_ops::add_assign_product_with_base(&mut *acc, &gamma, &base_val);
        col += 1;
    }
    let block_end = LEAF_WORDS.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
    if block_end > LEAF_WORDS {
        hash_buf.zero_range(LEAF_WORDS, block_end);
    }
    let buf = hash_buf.assume_init_subarray::<BUF_SIZE>();
    hash_leaf_data_into_state(hasher, buf, LEAF_WORDS);
    if !verify_merkle_path::<I>(hasher, query_index, depth, cap, nd_source) {
        return Err(E::whir_merkle_path_failed(query));
    }
    Ok(())
}
#[doc = r" [`process_oracle_query_single_value`] under a pruned Merkle"]
#[doc = r" multiproof (see `process_oracle_query_multiproof`)."]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn process_oracle_query_single_value_multiproof<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const BUF_SIZE: usize,
    const LEAF_WORDS: usize,
    const MAX_DEPTH: usize,
>(
    hasher: &mut ::verifier_common::blake2s_u32::DelegatedBlake2sState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, BUF_SIZE>,
    num_columns: usize,
    stack: &mut MerkleMultiproofStack<MAX_DEPTH>,
    tree_index: usize,
    prev_index_equal: bool,
    next_index: usize,
    depth: usize,
    cap: &[u32],
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    acc: &mut BabyBearExt4,
    query: usize,
    nd_source: &mut I,
) -> Result<(), E::Error> {
    use verifier_common::whir::hash_leaf_data_into_state;
    let buf = hash_buf.assume_init_subarray_mut::<BUF_SIZE>();
    let mut col = 0;
    while col < num_columns {
        let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
        let raw = read_reduced_field_el::<I>(nd_source);
        *buf.get_unchecked_mut(col) = raw.as_u32_raw_repr();
        let base_val = raw;
        field_ops::add_assign_product_with_base(&mut *acc, &gamma, &base_val);
        col += 1;
    }
    let block_end = LEAF_WORDS.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
    if block_end > LEAF_WORDS {
        hash_buf.zero_range(LEAF_WORDS, block_end);
    }
    let buf = hash_buf.assume_init_subarray::<BUF_SIZE>();
    hash_leaf_data_into_state(hasher, buf, LEAF_WORDS);
    if !verify_merkle_multiproof_leaf::<I, MAX_DEPTH>(
        hasher,
        stack,
        tree_index,
        prev_index_equal,
        next_index,
        depth,
        cap,
        nd_source,
    ) {
        return Err(E::whir_merkle_path_failed(query));
    }
    Ok(())
}
pub const MAX_OOD_SAMPLES: usize = 1usize;
const OOD_DRAW_BUF: usize = (MAX_OOD_SAMPLES * super::common::EXT_DEGREE + 1)
    .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
const OOD_COMMIT_BUF: usize = {
    let total = MAX_OOD_SAMPLES * super::common::EXT_DEGREE;
    (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
        * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
#[inline(always)]
pub fn read_ood_samples<I: NonDeterminismSource<BabyBearField>>(
    ts: &mut TranscriptState,
    committed_oracle: usize,
    ood_points: &mut LazyVec<BabyBearExt4, MAX_OOD_SAMPLES>,
    ood_values: &mut LazyVec<BabyBearExt4, MAX_OOD_SAMPLES>,
    nd_source: &mut I,
) {
    let num_ood = WHIR_NUM_OOD_SAMPLES[committed_oracle];
    let ood_pow_bits = WHIR_OOD_POW_BITS[committed_oracle];
    unsafe {
        ood_points.set_len(num_ood);
    }
    if ood_pow_bits > 0 {
        read_and_verify_pow::<I>(ts, ood_pow_bits, nd_source);
        super::common::draw_field_els_into_after_pow::<OOD_DRAW_BUF>(ts, ood_points.as_mut_slice());
    } else {
        super::common::draw_field_els_into::<OOD_DRAW_BUF>(ts, ood_points.as_mut_slice());
    }
    let ood_data_words = num_ood * super::common::EXT_DEGREE;
    let mut ood_buf = CommitBuf::<OOD_COMMIT_BUF>::new();
    let mut i = 0;
    while i < ood_data_words {
        ood_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
        i += 1;
    }
    unsafe {
        let values: &[BabyBearExt4] = ood_buf.data_as::<BabyBearExt4>(num_ood);
        let mut j = 0;
        while j < num_ood {
            ood_values.push(*values.get_unchecked(j));
            j += 1;
        }
    }
    ts.commit(&mut ood_buf, ood_data_words);
}
#[inline(always)]
pub fn accumulate_ood_samples<const MAX_POW: usize, const MAX_OOD: usize>(
    accumulator: &mut ::verifier_common::whir::WhirAccumulator<
        BabyBearField,
        BabyBearExt4,
        MAX_POW,
        MAX_OOD,
    >,
    ood_points: &LazyVec<BabyBearExt4, MAX_OOD_SAMPLES>,
    ood_values: &LazyVec<BabyBearExt4, MAX_OOD_SAMPLES>,
    delinearization_challenge: BabyBearExt4,
) -> (BabyBearExt4, BabyBearExt4) {
    let mut claim_correction = BabyBearExt4::ZERO;
    let mut current = delinearization_challenge;
    let num_ood = ood_points.len();
    let mut j = 0;
    while j < num_ood {
        if j > 0 {
            field_ops::mul_assign(&mut current, &delinearization_challenge);
        }
        push_whir_pow_entry(accumulator, *ood_points.get(j), current);
        let mut t = *ood_values.get(j);
        field_ops::mul_assign(&mut t, &current);
        field_ops::add_assign(&mut claim_correction, &t);
        j += 1;
    }
    (claim_correction, current)
}
const INITIAL_QUERY_INDEX_BITS: usize = 23usize;
const INITIAL_NUM_QUERIES: usize = 174usize;
#[doc = r" Whether this build opens the base queries as a pruned Merkle"]
#[doc = r" multiproof (`BlakeMode::merkle_multiproofs`, decided at compile"]
#[doc = r" time for the build's blake implementation)."]
const INITIAL_MERKLE_MULTIPROOF: bool =
    ::verifier_common::BLAKE_MODE.merkle_multiproofs(INITIAL_NUM_QUERIES, WHIR_CAP_SIZE);
const INITIAL_POW_BITS: u32 = 28u32;
const INITIAL_DRAW_WORDS: usize = 128usize;
const INITIAL_RS_DOMAIN_LOG2: usize = 23usize;
const NUM_COSETS: usize = 2usize;
const NUM_COSETS_LOG2: usize = 1usize;
const COSET_TREE_SIZE: usize = 4194304usize;
pub fn verify_initial_whir_round<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    batching_challenge: BabyBearExt4,
    base_layer_claims: &[BabyBearExt4],
    z_initial: &[BabyBearExt4],
    accumulator: &mut ::verifier_common::whir::WhirAccumulator<
        BabyBearField,
        BabyBearExt4,
        MAX_POW_ENTRIES,
        WHIR_OOD_ENTRIES,
    >,
    nd_source: &mut I,
) -> Result<(BabyBearExt4, [u32; WHIR_CAP_WORDS]), E::Error> {
    unsafe {
        let gamma_powers: [BabyBearExt4; TOTAL_ORACLE_COLS] =
            materialize_gamma_powers(batching_challenge);
        let mut claim = BabyBearExt4::ZERO;
        {
            let mut col_idx = 0;
            while col_idx < TOTAL_ORACLE_COLS {
                let eval: BabyBearExt4 = *base_layer_claims.get_unchecked(col_idx);
                let mut term = *gamma_powers.get_unchecked(col_idx);
                field_ops::mul_assign(&mut term, &eval);
                field_ops::add_assign(&mut claim, &term);
                col_idx += 1;
            }
        }
        const CAP_COMMIT_BUF: usize = {
            let total = WHIR_CAP_WORDS;
            (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
                * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        let intermediate_cap =
            read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(ts, nd_source);
        let mut ood_points: LazyVec<BabyBearExt4, MAX_OOD_SAMPLES> = LazyVec::new();
        let mut ood_values: LazyVec<BabyBearExt4, MAX_OOD_SAMPLES> = LazyVec::new();
        read_ood_samples::<I>(ts, 0, &mut ood_points, &mut ood_values, nd_source);
        read_and_verify_pow::<I>(ts, INITIAL_POW_BITS, nd_source);
        let query_indices = draw_query_indices::<INITIAL_NUM_QUERIES, INITIAL_DRAW_WORDS>(
            ts,
            INITIAL_NUM_QUERIES,
            INITIAL_QUERY_INDEX_BITS,
            INITIAL_DRAW_WORDS,
        );
        let delinearization_challenge = draw_fresh_single_field_el(ts);
        let (mut claim_correction, mut current_delinearization_challenge) = accumulate_ood_samples(
            accumulator,
            &ood_points,
            &ood_values,
            delinearization_challenge,
        );
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[INITIAL_RS_DOMAIN_LOG2];
        let extended_generator_inv =
            BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[INITIAL_RS_DOMAIN_LOG2];
        let mut tree_indices: LazyVec<usize, INITIAL_NUM_QUERIES> = LazyVec::new();
        {
            let mut q = 0;
            while q < INITIAL_NUM_QUERIES {
                let query_index = *query_indices.get(q);
                tree_indices.push(compute_tree_index(
                    query_index,
                    NUM_COSETS,
                    NUM_COSETS_LOG2,
                    COSET_TREE_SIZE,
                ));
                q += 1;
            }
        }
        let mut perm: LazyVec<usize, INITIAL_NUM_QUERIES> = LazyVec::new();
        let mut sorted: LazyVec<usize, INITIAL_NUM_QUERIES> = LazyVec::new();
        sort_queries_by_tree_index::<INITIAL_NUM_QUERIES>(
            &tree_indices,
            INITIAL_QUERY_INDEX_BITS,
            &mut perm,
            &mut sorted,
        );
        let mut delin_powers: LazyVec<BabyBearExt4, INITIAL_NUM_QUERIES> = LazyVec::new();
        {
            let mut q = 0;
            while q < INITIAL_NUM_QUERIES {
                field_ops::mul_assign(
                    &mut current_delinearization_challenge,
                    &delinearization_challenge,
                );
                delin_powers.push(current_delinearization_challenge);
                q += 1;
            }
        }
        let mut multiproof_stack_0 = MerkleMultiproofStack::<19usize>::new();
        let mut multiproof_stack_1 = MerkleMultiproofStack::<19usize>::new();
        let mut multiproof_stack_2 = MerkleMultiproofStack::<19usize>::new();
        let mut j = 0;
        while j < INITIAL_NUM_QUERIES {
            let q = *perm.get(j);
            let tree_index = *sorted.get(j);
            let prev_index_equal = j > 0 && *sorted.get(j - 1) == tree_index;
            let next_index = if j + 1 < INITIAL_NUM_QUERIES {
                *sorted.get(j + 1)
            } else {
                NO_NEXT_INDEX
            };
            let query_index = *query_indices.get(q);
            let current_delinearization_challenge = *delin_powers.get(q);
            let base_root_inv = extended_generator_inv.pow(query_index as u32);
            let mut acc0 = BabyBearExt4::ZERO;
            if INITIAL_MERKLE_MULTIPROOF {
                process_oracle_query_single_value_multiproof::<
                    I,
                    E,
                    WHIR_HASH_BUF_SIZE,
                    91usize,
                    19usize,
                >(
                    &mut ts.hasher,
                    hash_buf,
                    91usize,
                    &mut multiproof_stack_0,
                    tree_index,
                    prev_index_equal,
                    next_index,
                    19usize,
                    initial_transcript.memory_caps_slice(),
                    &gamma_powers[..],
                    0usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
                process_oracle_query_single_value_multiproof::<
                    I,
                    E,
                    WHIR_HASH_BUF_SIZE,
                    175usize,
                    19usize,
                >(
                    &mut ts.hasher,
                    hash_buf,
                    175usize,
                    &mut multiproof_stack_1,
                    tree_index,
                    prev_index_equal,
                    next_index,
                    19usize,
                    initial_transcript.witness_caps_slice(),
                    &gamma_powers[..],
                    91usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
                process_oracle_query_single_value_multiproof::<
                    I,
                    E,
                    WHIR_HASH_BUF_SIZE,
                    8usize,
                    19usize,
                >(
                    &mut ts.hasher,
                    hash_buf,
                    8usize,
                    &mut multiproof_stack_2,
                    tree_index,
                    prev_index_equal,
                    next_index,
                    19usize,
                    initial_transcript.setup_caps_slice(),
                    &gamma_powers[..],
                    266usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
            } else {
                process_oracle_query_single_value::<I, E, WHIR_HASH_BUF_SIZE, 91usize>(
                    &mut ts.hasher,
                    hash_buf,
                    91usize,
                    tree_index,
                    19usize,
                    initial_transcript.memory_caps_slice(),
                    &gamma_powers[..],
                    0usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
                process_oracle_query_single_value::<I, E, WHIR_HASH_BUF_SIZE, 175usize>(
                    &mut ts.hasher,
                    hash_buf,
                    175usize,
                    tree_index,
                    19usize,
                    initial_transcript.witness_caps_slice(),
                    &gamma_powers[..],
                    91usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
                process_oracle_query_single_value::<I, E, WHIR_HASH_BUF_SIZE, 8usize>(
                    &mut ts.hasher,
                    hash_buf,
                    8usize,
                    tree_index,
                    19usize,
                    initial_transcript.setup_caps_slice(),
                    &gamma_powers[..],
                    266usize,
                    &mut acc0,
                    q,
                    nd_source,
                )?;
            }
            let folded = acc0;
            let mut query_point_base = extended_generator.pow(query_index as u32);
            query_point_base.exp_power_of_2(WHIR_FOLD_STEPS[0]);
            push_whir_base_pow_entry(
                accumulator,
                query_point_base,
                current_delinearization_challenge,
            );
            let mut t = folded;
            field_ops::mul_assign(&mut t, &current_delinearization_challenge);
            field_ops::add_assign(&mut claim_correction, &t);
            j += 1;
        }
        field_ops::add_assign(&mut claim, &claim_correction);
        Ok((claim, intermediate_cap))
    }
}
use super::common::EXT_DEGREE;
use verifier_common::whir::{hash_leaf_data_into_state, verify_merkle_path};
pub const NUM_INTERNAL_ROUNDS: usize = 3usize;
const INTERNAL_QUERY_INDEX_BITS: [usize; NUM_INTERNAL_ROUNDS] = [21usize, 20usize, 17usize];
const INTERNAL_NUM_COSETS: [usize; NUM_INTERNAL_ROUNDS] = [32usize, 512usize, 2048usize];
const INTERNAL_NUM_COSETS_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [5usize, 9usize, 11usize];
const INTERNAL_COSET_TREE_SIZE: [usize; NUM_INTERNAL_ROUNDS] = [65536usize, 2048usize, 64usize];
const INTERNAL_RS_DOMAIN_LOG2: [usize; NUM_INTERNAL_ROUNDS] = [27usize, 25usize, 22usize];
const MAX_INTERNAL_FOLD_STEPS: usize = 6usize;
const MAX_INTERNAL_VALUES_PER_LEAF: usize = 64usize;
const MAX_INTERNAL_LEAF_EXT_WORDS: usize = MAX_INTERNAL_VALUES_PER_LEAF * EXT_DEGREE;
const INTERNAL_HASH_BUF_SIZE: usize = MAX_INTERNAL_LEAF_EXT_WORDS
    .div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS)
    * BLAKE2S_BLOCK_SIZE_U32_WORDS;
const MAX_INTERNAL_NUM_QUERIES: usize = 31usize;
const MAX_INTERNAL_DRAW_WORDS: usize = 24usize;
#[doc = r" Bit `ir` set: this build opens internal round `ir + 1`'s queries"]
#[doc = r" as a pruned Merkle multiproof (`BlakeMode::merkle_multiproofs`,"]
#[doc = r" decided at compile time for the build's blake implementation)."]
#[doc = r" A bitmask, not a `[bool; N]`: a runtime-indexed byte array would"]
#[doc = r" need a byte load, which the reduced machine has not."]
const INTERNAL_MERKLE_MULTIPROOF_MASK: usize = {
    let mut mask = 0;
    let mut ir = 0;
    while ir < NUM_INTERNAL_ROUNDS {
        if ::verifier_common::BLAKE_MODE.merkle_multiproofs(WHIR_QUERIES[ir + 1], WHIR_CAP_SIZE) {
            mask |= 1 << ir;
        }
        ir += 1;
    }
    mask
};
const MAX_INTERNAL_ORACLE_DEPTH: usize = {
    let mut max = 0;
    let mut i = 0;
    while i < NUM_INTERNAL_ROUNDS {
        if WHIR_ORACLE_DEPTHS[i] > max {
            max = WHIR_ORACLE_DEPTHS[i];
        }
        i += 1;
    }
    max
};
const INTERNAL_DRAW_WORDS: [usize; NUM_INTERNAL_ROUNDS] = [24usize, 16usize, 16usize];
pub fn verify_internal_whir_round<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
    round_idx: usize,
    z_initial: &[BabyBearExt4],
    accumulator: &mut ::verifier_common::whir::WhirAccumulator<
        BabyBearField,
        BabyBearExt4,
        MAX_POW_ENTRIES,
        WHIR_OOD_ENTRIES,
    >,
    nd_source: &mut I,
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
            let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(
                ts,
                claim,
                round,
                WHIR_FOLDING_POW_BITS[round_idx],
                nd_source,
            )?;
            claim = new_claim;
            folding_challenges.push(alpha);
            fold_whir_accumulator(accumulator, alpha, z_initial);
            round += 1;
        }
        const CAP_COMMIT_BUF: usize = {
            let total = WHIR_CAP_WORDS;
            (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
                * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        let intermediate_cap =
            read_commit_return_merkle_cap::<I, WHIR_CAP_WORDS, CAP_COMMIT_BUF>(ts, nd_source);
        let mut ood_points: LazyVec<BabyBearExt4, MAX_OOD_SAMPLES> = LazyVec::new();
        let mut ood_values: LazyVec<BabyBearExt4, MAX_OOD_SAMPLES> = LazyVec::new();
        read_ood_samples::<I>(ts, round_idx, &mut ood_points, &mut ood_values, nd_source);
        read_and_verify_pow::<I>(ts, WHIR_POW_BITS[round_idx], nd_source);
        let query_index_bits = INTERNAL_QUERY_INDEX_BITS[ir];
        let draw_words = INTERNAL_DRAW_WORDS[ir];
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            ts,
            num_queries,
            query_index_bits,
            draw_words,
        );
        let delinearization_challenge = draw_fresh_single_field_el(ts);
        let (mut claim_correction, mut current_delinearization_challenge) = accumulate_ood_samples(
            accumulator,
            &ood_points,
            &ood_values,
            delinearization_challenge,
        );
        let rs_domain_log2 = INTERNAL_RS_DOMAIN_LOG2[ir];
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[rs_domain_log2];
        let num_cosets = INTERNAL_NUM_COSETS[ir];
        let num_cosets_log2 = INTERNAL_NUM_COSETS_LOG2[ir];
        let coset_tree_size = INTERNAL_COSET_TREE_SIZE[ir];
        let oracle_depth = WHIR_ORACLE_DEPTHS[round_idx - 1];
        let mut monomial_weights = LazyVec::<BabyBearExt4, MAX_INTERNAL_VALUES_PER_LEAF>::new();
        precompute_monomial_tensor(folding_challenges.as_slice(), &mut monomial_weights);
        let mut tree_indices: LazyVec<usize, MAX_INTERNAL_NUM_QUERIES> = LazyVec::new();
        {
            let mut q = 0;
            while q < num_queries {
                let query_index = *query_indices.get(q);
                tree_indices.push(compute_tree_index(
                    query_index,
                    num_cosets,
                    num_cosets_log2,
                    coset_tree_size,
                ));
                q += 1;
            }
        }
        let mut perm: LazyVec<usize, MAX_INTERNAL_NUM_QUERIES> = LazyVec::new();
        let mut sorted: LazyVec<usize, MAX_INTERNAL_NUM_QUERIES> = LazyVec::new();
        sort_queries_by_tree_index::<MAX_INTERNAL_NUM_QUERIES>(
            &tree_indices,
            query_index_bits,
            &mut perm,
            &mut sorted,
        );
        let mut delin_powers: LazyVec<BabyBearExt4, MAX_INTERNAL_NUM_QUERIES> = LazyVec::new();
        {
            let mut q = 0;
            while q < num_queries {
                field_ops::mul_assign(
                    &mut current_delinearization_challenge,
                    &delinearization_challenge,
                );
                delin_powers.push(current_delinearization_challenge);
                q += 1;
            }
        }
        let mut multiproof_stack = MerkleMultiproofStack::<MAX_INTERNAL_ORACLE_DEPTH>::new();
        let mut j = 0;
        while j < num_queries {
            let q = *perm.get(j);
            let tree_index = *sorted.get(j);
            let prev_index_equal = j > 0 && *sorted.get(j - 1) == tree_index;
            let next_index = if j + 1 < num_queries {
                *sorted.get(j + 1)
            } else {
                NO_NEXT_INDEX
            };
            let query_index = *query_indices.get(q);
            let current_delinearization_challenge = *delin_powers.get(q);
            {
                let mut i = 0;
                while i < leaf_ext_words {
                    let mut k = 0;
                    while k < EXT_DEGREE {
                        hash_buf.write(
                            i + k,
                            read_reduced_field_el::<I>(nd_source).as_u32_raw_repr(),
                        );
                        k += 1;
                    }
                    i += EXT_DEGREE;
                }
            }
            let block_end = (leaf_ext_words).next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            hash_buf.zero_range(leaf_ext_words, block_end);
            let init_buf = hash_buf.assume_init_subarray::<INTERNAL_HASH_BUF_SIZE>();
            hash_leaf_data_into_state(&mut ts.hasher, init_buf, leaf_ext_words);
            let merkle_ok = if (INTERNAL_MERKLE_MULTIPROOF_MASK >> ir) & 1 == 1 {
                verify_merkle_multiproof_leaf::<I, MAX_INTERNAL_ORACLE_DEPTH>(
                    &mut ts.hasher,
                    &mut multiproof_stack,
                    tree_index,
                    prev_index_equal,
                    next_index,
                    oracle_depth,
                    prev_oracle_cap,
                    nd_source,
                )
            } else {
                verify_merkle_path::<I>(
                    &mut ts.hasher,
                    tree_index,
                    oracle_depth,
                    prev_oracle_cap,
                    nd_source,
                )
            };
            if !merkle_ok {
                return Err(E::whir_merkle_path_failed(q));
            }
            let leaf: &[BabyBearExt4] = unsafe { init_buf.transmute_subslice(0, values_per_leaf) };
            let folded = eval_multilinear_with_monomial_tensor(leaf, monomial_weights.as_slice());
            let mut query_point_base = extended_generator.pow(query_index as u32);
            query_point_base.exp_power_of_2(fold_steps);
            push_whir_base_pow_entry(
                accumulator,
                query_point_base,
                current_delinearization_challenge,
            );
            let mut t = folded;
            field_ops::mul_assign(&mut t, &current_delinearization_challenge);
            field_ops::add_assign(&mut claim_correction, &t);
            j += 1;
        }
        field_ops::add_assign(&mut claim, &claim_correction);
        Ok((claim, intermediate_cap))
    }
}
const FINAL_FOLD_STEPS: usize = 5usize;
const FINAL_NUM_QUERIES: usize = 12usize;
const FINAL_VALUES_PER_LEAF: usize = 32usize;
const FINAL_LEAF_EXT_WORDS: usize = FINAL_VALUES_PER_LEAF * EXT_DEGREE;
const FINAL_HASH_BUF_SIZE: usize =
    FINAL_LEAF_EXT_WORDS.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS;
const FINAL_QUERY_INDEX_BITS: usize = 14usize;
const FINAL_RS_DOMAIN_LOG2: usize = 19usize;
const FINAL_NUM_COSETS: usize = 8192usize;
const FINAL_NUM_COSETS_LOG2: usize = 13usize;
const FINAL_COSET_TREE_SIZE: usize = 2usize;
const FINAL_DRAW_WORDS: usize = 8usize;
const FINAL_POW_BITS: u32 = 25u32;
const FINAL_FOLDING_POW_BITS: u32 = 23u32;
const FINAL_ORACLE_DEPTH_IDX: usize = 3usize;
const FINAL_ORACLE_DEPTH: usize = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];
#[doc = r" Whether this build opens the final queries as a pruned Merkle"]
#[doc = r" multiproof (`BlakeMode::merkle_multiproofs`, decided at compile"]
#[doc = r" time for the build's blake implementation)."]
const FINAL_MERKLE_MULTIPROOF: bool =
    ::verifier_common::BLAKE_MODE.merkle_multiproofs(FINAL_NUM_QUERIES, WHIR_CAP_SIZE);
pub fn verify_final_whir_round<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    ts: &mut TranscriptState,
    hash_buf: &mut AlignedArray64<MaybeUninit<u32>, WHIR_HASH_BUF_SIZE>,
    claim: BabyBearExt4,
    prev_oracle_cap: &[u32; WHIR_CAP_WORDS],
    z_initial: &[BabyBearExt4],
    accumulator: &mut ::verifier_common::whir::WhirAccumulator<
        BabyBearField,
        BabyBearExt4,
        MAX_POW_ENTRIES,
        WHIR_OOD_ENTRIES,
    >,
    nd_source: &mut I,
) -> Result<(), E::Error> {
    unsafe {
        let mut claim = claim;
        let mut folding_challenges: LazyVec<BabyBearExt4, FINAL_FOLD_STEPS> = LazyVec::new();
        let mut round = 0;
        while round < FINAL_FOLD_STEPS {
            let (new_claim, alpha) = verify_whir_sumcheck_step::<I, E>(
                ts,
                claim,
                round,
                FINAL_FOLDING_POW_BITS,
                nd_source,
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
        debug_assert_eq!(
            accumulator.pow_entries.len() + accumulator.base_pow_entries.len(),
            MAX_POW_ENTRIES,
        );
        const FINAL_MONOMIALS_DATA_WORDS: usize = FINAL_MONOMIALS_LEN * EXT_DEGREE;
        const FINAL_MONOMIALS_COMMIT_BUF: usize = {
            let total = FINAL_MONOMIALS_DATA_WORDS;
            (total + BLAKE2S_BLOCK_SIZE_U32_WORDS - 1) / BLAKE2S_BLOCK_SIZE_U32_WORDS
                * BLAKE2S_BLOCK_SIZE_U32_WORDS
        };
        let mut monomials_buf = CommitBuf::<FINAL_MONOMIALS_COMMIT_BUF>::new();
        {
            let mut i = 0;
            while i < FINAL_MONOMIALS_DATA_WORDS {
                monomials_buf
                    .data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                i += 1;
            }
        }
        ts.commit(&mut monomials_buf, FINAL_MONOMIALS_DATA_WORDS);
        let monomials: &[BabyBearExt4] = monomials_buf.data_as::<BabyBearExt4>(FINAL_MONOMIALS_LEN);
        read_and_verify_pow::<I>(ts, FINAL_POW_BITS, nd_source);
        let query_indices = draw_query_indices::<MAX_INTERNAL_NUM_QUERIES, MAX_INTERNAL_DRAW_WORDS>(
            ts,
            FINAL_NUM_QUERIES,
            FINAL_QUERY_INDEX_BITS,
            FINAL_DRAW_WORDS,
        );
        let extended_generator = BabyBearField::TWO_ADICITY_GENERATORS[FINAL_RS_DOMAIN_LOG2];
        let oracle_depth = WHIR_ORACLE_DEPTHS[FINAL_ORACLE_DEPTH_IDX];
        let mut monomial_weights = LazyVec::<BabyBearExt4, FINAL_VALUES_PER_LEAF>::new();
        precompute_monomial_tensor(folding_challenges.as_slice(), &mut monomial_weights);
        let mut folded_values: LazyVec<BabyBearExt4, FINAL_NUM_QUERIES> = LazyVec::new();
        let mut query_base_roots: LazyVec<BabyBearField, FINAL_NUM_QUERIES> = LazyVec::new();
        let mut tree_indices: LazyVec<usize, FINAL_NUM_QUERIES> = LazyVec::new();
        {
            let mut q = 0;
            while q < FINAL_NUM_QUERIES {
                let query_index = *query_indices.get(q);
                tree_indices.push(compute_tree_index(
                    query_index,
                    FINAL_NUM_COSETS,
                    FINAL_NUM_COSETS_LOG2,
                    FINAL_COSET_TREE_SIZE,
                ));
                q += 1;
            }
        }
        let mut perm: LazyVec<usize, FINAL_NUM_QUERIES> = LazyVec::new();
        let mut sorted: LazyVec<usize, FINAL_NUM_QUERIES> = LazyVec::new();
        sort_queries_by_tree_index::<FINAL_NUM_QUERIES>(
            &tree_indices,
            FINAL_QUERY_INDEX_BITS,
            &mut perm,
            &mut sorted,
        );
        let mut multiproof_stack = MerkleMultiproofStack::<FINAL_ORACLE_DEPTH>::new();
        let mut j = 0;
        while j < FINAL_NUM_QUERIES {
            let q = *perm.get(j);
            let tree_index = *sorted.get(j);
            let prev_index_equal = j > 0 && *sorted.get(j - 1) == tree_index;
            let next_index = if j + 1 < FINAL_NUM_QUERIES {
                *sorted.get(j + 1)
            } else {
                NO_NEXT_INDEX
            };
            let query_index = *query_indices.get(q);
            let base_root = extended_generator.pow(query_index as u32);
            {
                let mut i = 0;
                while i < FINAL_LEAF_EXT_WORDS {
                    let mut k = 0;
                    while k < EXT_DEGREE {
                        hash_buf.write(
                            i + k,
                            read_reduced_field_el::<I>(nd_source).as_u32_raw_repr(),
                        );
                        k += 1;
                    }
                    i += EXT_DEGREE;
                }
            }
            let block_end = (FINAL_LEAF_EXT_WORDS).next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            hash_buf.zero_range(FINAL_LEAF_EXT_WORDS, block_end);
            let init_buf = hash_buf.assume_init_subarray::<FINAL_HASH_BUF_SIZE>();
            hash_leaf_data_into_state(&mut ts.hasher, init_buf, FINAL_LEAF_EXT_WORDS);
            let merkle_ok = if FINAL_MERKLE_MULTIPROOF {
                verify_merkle_multiproof_leaf::<I, FINAL_ORACLE_DEPTH>(
                    &mut ts.hasher,
                    &mut multiproof_stack,
                    tree_index,
                    prev_index_equal,
                    next_index,
                    oracle_depth,
                    prev_oracle_cap,
                    nd_source,
                )
            } else {
                verify_merkle_path::<I>(
                    &mut ts.hasher,
                    tree_index,
                    oracle_depth,
                    prev_oracle_cap,
                    nd_source,
                )
            };
            if !merkle_ok {
                return Err(E::whir_merkle_path_failed(q));
            }
            let leaf: &[BabyBearExt4] =
                unsafe { init_buf.transmute_subslice(0, FINAL_VALUES_PER_LEAF) };
            let folded = eval_multilinear_with_monomial_tensor(leaf, monomial_weights.as_slice());
            folded_values.push(folded);
            query_base_roots.push(base_root);
            j += 1;
        }
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
        let mut f_m_buf = LazyVec::<BabyBearExt4, FINAL_MONOMIALS_LEN>::new();
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
        {
            let n = accumulator.base_pow_entries.len();
            let mut ei = 0;
            while ei < n {
                let entry = accumulator.base_pow_entries.get_unchecked(ei);
                let s = entry.current_scalar;
                let mut eval = *monomials.get_unchecked(FINAL_MONOMIALS_LEN - 1);
                let mut j = FINAL_MONOMIALS_LEN - 1;
                while j > 0 {
                    j -= 1;
                    let mut t = *monomials.get_unchecked(j);
                    field_ops::add_assign_product_with_base(&mut t, &eval, &s);
                    eval = t;
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
#[cfg(feature = "verifier_stats")]
const _: () = assert!(
    NUM_INTERNAL_ROUNDS + 1
        < [
            "WHIR SINGLE ROUND 0",
            "WHIR SINGLE ROUND 1",
            "WHIR SINGLE ROUND 2",
            "WHIR SINGLE ROUND 3",
            "WHIR SINGLE ROUND 4",
            "WHIR SINGLE ROUND 5",
            "WHIR SINGLE ROUND 6",
            "WHIR SINGLE ROUND 7",
            "WHIR SINGLE ROUND 8",
            "WHIR SINGLE ROUND 9",
            "WHIR SINGLE ROUND 10",
            "WHIR SINGLE ROUND 11",
            "WHIR SINGLE ROUND 12",
            "WHIR SINGLE ROUND 13",
            "WHIR SINGLE ROUND 14",
            "WHIR SINGLE ROUND 15",
            "WHIR SINGLE ROUND 16",
            "WHIR SINGLE ROUND 17",
            "WHIR SINGLE ROUND 18",
            "WHIR SINGLE ROUND 19",
            "WHIR SINGLE ROUND 20",
            "WHIR SINGLE ROUND 21",
            "WHIR SINGLE ROUND 22",
            "WHIR SINGLE ROUND 23",
            "WHIR SINGLE ROUND 24",
            "WHIR SINGLE ROUND 25",
            "WHIR SINGLE ROUND 26",
            "WHIR SINGLE ROUND 27",
        ]
        .len(),
    "WHIR stats labels array is too small for NUM_INTERNAL_ROUNDS"
);
pub const WHIR_HASH_BUF_SIZE: usize = 256usize;
pub fn verify_whir<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut TranscriptState,
    batching_challenge: BabyBearExt4,
    base_layer_claims: &[BabyBearExt4],
    z_initial: &[BabyBearExt4],
    nd_source: &mut I,
) -> Result<(), E::Error> {
    let mut hash_buf = AlignedArray64::<u32, WHIR_HASH_BUF_SIZE>::new_uninit();
    let mut accumulator = ::verifier_common::whir::WhirAccumulator::<
        BabyBearField,
        BabyBearExt4,
        MAX_POW_ENTRIES,
        WHIR_OOD_ENTRIES,
    >::new(BabyBearExt4::ONE);
    let (mut claim, mut cap) = verify_initial_whir_round::<I, E>(
        initial_transcript,
        ts,
        &mut hash_buf,
        batching_challenge,
        base_layer_claims,
        z_initial,
        &mut accumulator,
        nd_source,
    )?;
    #[cfg(feature = "verifier_stats")]
    verifier_common::stats::log("WHIR BATCHED ROUND 0");
    let mut round_idx = 1;
    while round_idx <= NUM_INTERNAL_ROUNDS {
        let (new_claim, new_cap) = verify_internal_whir_round::<I, E>(
            ts,
            &mut hash_buf,
            claim,
            &cap,
            round_idx,
            z_initial,
            &mut accumulator,
            nd_source,
        )?;
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log(
            [
                "WHIR SINGLE ROUND 0",
                "WHIR SINGLE ROUND 1",
                "WHIR SINGLE ROUND 2",
                "WHIR SINGLE ROUND 3",
                "WHIR SINGLE ROUND 4",
                "WHIR SINGLE ROUND 5",
                "WHIR SINGLE ROUND 6",
                "WHIR SINGLE ROUND 7",
                "WHIR SINGLE ROUND 8",
                "WHIR SINGLE ROUND 9",
                "WHIR SINGLE ROUND 10",
                "WHIR SINGLE ROUND 11",
                "WHIR SINGLE ROUND 12",
                "WHIR SINGLE ROUND 13",
                "WHIR SINGLE ROUND 14",
                "WHIR SINGLE ROUND 15",
                "WHIR SINGLE ROUND 16",
                "WHIR SINGLE ROUND 17",
                "WHIR SINGLE ROUND 18",
                "WHIR SINGLE ROUND 19",
                "WHIR SINGLE ROUND 20",
                "WHIR SINGLE ROUND 21",
                "WHIR SINGLE ROUND 22",
                "WHIR SINGLE ROUND 23",
                "WHIR SINGLE ROUND 24",
                "WHIR SINGLE ROUND 25",
                "WHIR SINGLE ROUND 26",
                "WHIR SINGLE ROUND 27",
            ][round_idx],
        );
        claim = new_claim;
        cap = new_cap;
        round_idx += 1;
    }
    verify_final_whir_round::<I, E>(
        ts,
        &mut hash_buf,
        claim,
        &cap,
        z_initial,
        &mut accumulator,
        nd_source,
    )?;
    #[cfg(feature = "verifier_stats")]
    verifier_common::stats::log(
        [
            "WHIR SINGLE ROUND 0",
            "WHIR SINGLE ROUND 1",
            "WHIR SINGLE ROUND 2",
            "WHIR SINGLE ROUND 3",
            "WHIR SINGLE ROUND 4",
            "WHIR SINGLE ROUND 5",
            "WHIR SINGLE ROUND 6",
            "WHIR SINGLE ROUND 7",
            "WHIR SINGLE ROUND 8",
            "WHIR SINGLE ROUND 9",
            "WHIR SINGLE ROUND 10",
            "WHIR SINGLE ROUND 11",
            "WHIR SINGLE ROUND 12",
            "WHIR SINGLE ROUND 13",
            "WHIR SINGLE ROUND 14",
            "WHIR SINGLE ROUND 15",
            "WHIR SINGLE ROUND 16",
            "WHIR SINGLE ROUND 17",
            "WHIR SINGLE ROUND 18",
            "WHIR SINGLE ROUND 19",
            "WHIR SINGLE ROUND 20",
            "WHIR SINGLE ROUND 21",
            "WHIR SINGLE ROUND 22",
            "WHIR SINGLE ROUND 23",
            "WHIR SINGLE ROUND 24",
            "WHIR SINGLE ROUND 25",
            "WHIR SINGLE ROUND 26",
            "WHIR SINGLE ROUND 27",
        ][NUM_INTERNAL_ROUNDS + 1],
    );
    Ok(())
}
