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
use super::common::EXT_DEGREE;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::{DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS};
#[doc = r" Number of rounds of every same-size GKR layer sumcheck = the number"]
#[doc = r" of GKR claim-point coordinates: log2 of the LOGICAL (trace-length)"]
#[doc = r" polynomials. Packing does not change it."]
pub const GKR_ROUNDS: usize = 24usize;
#[doc = r" Capacity of the claim-point buffers: the GKR point plus the"]
#[doc = r" `PACK_LOG2` coordinates appended after the GKR phase for the packed"]
#[doc = r" base commitment (`TRACE_LEN_LOG2 + pack_log2`, the committed column"]
#[doc = r" size the WHIR point has). Equals `GKR_ROUNDS` when unpacked."]
pub const CLAIM_POINT_CAPACITY: usize = 24usize;
pub const TRACE_LEN_LOG2: u32 = 24u32;
pub const GKR_ADDRS: usize = 34usize;
pub const GKR_EVALS: usize = 32usize;
pub const INIT_AND_TEARDOWN_SETS: usize = 8usize;
pub const EXTERNAL_CHALLENGES_FLATTENED_SIZE: usize = EXT_DEGREE * (6usize + 1);
pub const CAP_SIZE: usize = 16usize;
pub const NUM_MEMORY_COMMITS: usize = 1usize;
pub const NUM_WITNESS_COMMITS: usize = 0usize;
pub const NUM_SETUP_COMMITS: usize = 0usize;
pub const PADDING_WORDS: usize = {
    let mut total = 8usize;
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
    let dim_reducing = 34usize * DIM_REDUCE_EVAL_POINTS * EXT_DEGREE;
    let standard = 34usize * STANDARD_EVAL_POINTS * EXT_DEGREE;
    let evals = 32usize * EXT_DEGREE;
    let max_data = if dim_reducing > standard {
        dim_reducing
    } else {
        standard
    };
    let max_data = if max_data > evals { max_data } else { evals };
    let total = max_data;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const GKR_COMMIT_BUF: usize = {
    let total = SUMCHECK_POLY_COEFFS * EXT_DEGREE;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const GKR_EVALS_COMMIT_BUF: usize = {
    let total = 32usize * EXT_DEGREE;
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
pub const WHIR_QUERIES: [usize; 6usize] = [174usize, 39usize, 20usize, 16usize, 13usize, 11usize];
pub const WHIR_POW_BITS: [u32; 6usize] = [28u32, 26u32, 25u32, 24u32, 25u32, 26u32];
#[doc = r" Per round: PoW bits gating each folding-challenge draw (0 = plain draws)."]
pub const WHIR_FOLDING_POW_BITS: [u32; 6usize] = [0u32, 24u32, 22u32, 22u32, 22u32, 23u32];
#[doc = r" Per intermediate oracle: its out-of-domain sample count and the PoW"]
#[doc = r" bits gating the OOD point draw (0 = a plain draw)."]
pub const WHIR_NUM_OOD_SAMPLES: [usize; 5usize] = [1usize, 1usize, 1usize, 1usize, 1usize];
pub const WHIR_OOD_POW_BITS: [u32; 5usize] = [9u32, 5u32, 2u32, 0u32, 0u32];
#[doc = r" Total OOD samples across the intermediate oracles (the accumulator's"]
#[doc = r" out-of-domain entry capacity)."]
pub const WHIR_OOD_ENTRIES: usize = 5usize;
pub const LOOKUP_CHALLENGES_POW_BITS: u32 = 0u32;
pub const BATCHED_PROXIMITY_POW_BITS: u32 = 9u32;
pub const MAX_POW_ENTRIES: usize = 267usize;
pub const FINAL_MONOMIALS_LEN: usize = 2usize;
pub const NUM_ORACLES: usize = 1usize;
pub const ORACLE_NUM_COLS: [usize; 1usize] = [32usize];
pub const ORACLE_DEPTHS: [usize; 1usize] = [20usize];
pub const TOTAL_ORACLE_COLS: usize = 32usize;
pub const WHIR_ORACLE_DEPTHS: [usize; 5usize] = [18usize, 17usize, 14usize, 12usize, 11usize];
pub const WHIR_CAP_SIZE: usize = 16usize;
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
    ::verifier_common::GKRVerifierOutput<BabyBearExt4, CLAIM_POINT_CAPACITY, GKR_ADDRS>;
pub type ConcreteVerifierOutput = ::verifier_common::VerifierOutput<
    BabyBearExt4,
    INIT_AND_TEARDOWN_SETS,
    CAP_SIZE,
    NUM_MEMORY_COMMITS,
    NUM_SETUP_COMMITS,
>;
