use super::common::EXT_DEGREE;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::{DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS};
pub const GKR_ROUNDS: usize = 24usize;
pub const GKR_ADDRS: usize = 83usize;
pub const GKR_EVALS: usize = 128usize;
pub const INIT_AND_TEARDOWN_SETS: usize = 0usize;
pub const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize = EXT_DEGREE * (6usize + 1);
pub const CAP_SIZE: usize = 16usize;
pub const NUM_MEMORY_COMMITS: usize = 1usize;
pub const NUM_WITNESS_COMMITS: usize = 1usize;
pub const NUM_SETUP_COMMITS: usize = 1usize;
pub const PADDING_WORDS: usize = {
    let mut total = 0usize;
    total += EXT_DEGREE
        * (::verifier_common::cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES
            + 1);
    total += CAP_SIZE
        * BLAKE2S_DIGEST_SIZE_U32_WORDS
        * (NUM_MEMORY_COMMITS + NUM_WITNESS_COMMITS + NUM_SETUP_COMMITS);
    let rem = total % BLAKE2S_BLOCK_SIZE_U32_WORDS;
    if rem == 0 {
        0
    } else {
        BLAKE2S_BLOCK_SIZE_U32_WORDS - rem
    }
};
pub const GKR_EVAL_BUF: usize = {
    let dim_reducing = 83usize * DIM_REDUCE_EVAL_POINTS * EXT_DEGREE;
    let standard = 83usize * STANDARD_EVAL_POINTS * EXT_DEGREE;
    let evals = 128usize * EXT_DEGREE;
    let max_data = if dim_reducing > standard {
        dim_reducing
    } else {
        standard
    };
    let max_data = if max_data > evals { max_data } else { evals };
    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + max_data;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const GKR_COMMIT_BUF: usize = {
    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + SUMCHECK_POLY_COEFFS * EXT_DEGREE;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const GKR_EVALS_COMMIT_BUF: usize = {
    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 128usize * EXT_DEGREE;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const DRAW_BUF_CAPACITY: usize = {
    let sumcheck = (5usize * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let lookup_after_pow = (2 * EXT_DEGREE + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    if sumcheck > lookup_after_pow {
        sumcheck
    } else {
        lookup_after_pow
    }
};
pub const WHIR_FOLD_STEPS: [usize; 6usize] = [1usize, 5usize, 5usize, 5usize, 4usize, 3usize];
pub const WHIR_QUERIES: [usize; 6usize] = [63usize, 17usize, 8usize, 5usize, 3usize, 3usize];
pub const WHIR_POW_BITS: [u32; 6usize] = [28u32, 20u32, 17u32, 10u32, 23u32, 23u32];
pub const LOOKUP_CHALLENGES_POW_BITS: u32 = 0u32;
pub const BATCHED_PROXIMITY_POW_BITS: u32 = 0u32;
pub const MAX_POW_ENTRIES: usize = 101usize;
pub const FINAL_MONOMIALS_LEN: usize = 2usize;
pub const NUM_ORACLES: usize = 3usize;
pub const ORACLE_NUM_COLS: [usize; 3usize] = [26usize, 24usize, 9usize];
pub const ORACLE_DEPTHS: [usize; 3usize] = [20usize, 20usize, 20usize];
pub const TOTAL_ORACLE_COLS: usize = 59usize;
pub const WHIR_ORACLE_DEPTHS: [usize; 5usize] = [18usize, 18usize, 18usize, 19usize, 16usize];
pub const WHIR_CAP_WORDS: usize = 128usize;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
pub type ConcreteInitialTranscript = ::verifier_common::InitialGKRTranscript<
    BabyBearExt4,
    INIT_AND_TEARDOWN_SETS,
    EXTERNAL_CHALLENGES_FLATTENED_SIZE,
    CAP_SIZE,
    NUM_MEMORY_COMMITS,
    NUM_WITNESS_COMMITS,
    NUM_SETUP_COMMITS,
    PADDING_WORDS,
>;
pub type ConcreteGKRVerifierOutput =
    ::verifier_common::GKRVerifierOutput<BabyBearExt4, GKR_ROUNDS, GKR_ADDRS>;
pub type ConcreteVerifierOutput = ::verifier_common::VerifierOutput<
    BabyBearExt4,
    INIT_AND_TEARDOWN_SETS,
    CAP_SIZE,
    NUM_MEMORY_COMMITS,
    NUM_SETUP_COMMITS,
>;
