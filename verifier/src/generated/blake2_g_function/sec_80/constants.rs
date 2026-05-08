use super::common::EXT_DEGREE;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::cs::definitions::{GKRAddress, VirtualSetupPoly};
use verifier_common::{DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS};
pub const GKR_ROUNDS: usize = 22usize;
pub const GKR_ADDRS: usize = 180usize;
pub const GKR_EVALS: usize = 96usize;
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
pub const GKR_MAX_POW: usize = 1usize;
pub const GKR_EVAL_BUF: usize = {
    let dim_reducing = 180usize * DIM_REDUCE_EVAL_POINTS * EXT_DEGREE;
    let standard = 180usize * STANDARD_EVAL_POINTS * EXT_DEGREE;
    let evals = 96usize * EXT_DEGREE;
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
    let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 96usize * EXT_DEGREE;
    total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
};
pub const DRAW_BUF_CAPACITY: usize =
    (5usize * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
pub const LAYER_0_SORTED_ADDRS: &[GKRAddress] = &[
    GKRAddress::BaseLayerWitness(0usize),
    GKRAddress::BaseLayerWitness(1usize),
    GKRAddress::BaseLayerWitness(2usize),
    GKRAddress::BaseLayerWitness(3usize),
    GKRAddress::BaseLayerWitness(7usize),
    GKRAddress::BaseLayerWitness(8usize),
    GKRAddress::BaseLayerWitness(10usize),
    GKRAddress::BaseLayerWitness(11usize),
    GKRAddress::BaseLayerWitness(12usize),
    GKRAddress::BaseLayerWitness(13usize),
    GKRAddress::BaseLayerWitness(20usize),
    GKRAddress::BaseLayerWitness(21usize),
    GKRAddress::BaseLayerWitness(22usize),
    GKRAddress::BaseLayerWitness(25usize),
    GKRAddress::BaseLayerWitness(26usize),
    GKRAddress::BaseLayerWitness(27usize),
    GKRAddress::BaseLayerWitness(28usize),
    GKRAddress::BaseLayerWitness(29usize),
    GKRAddress::BaseLayerWitness(30usize),
    GKRAddress::BaseLayerWitness(31usize),
    GKRAddress::BaseLayerWitness(34usize),
    GKRAddress::BaseLayerWitness(35usize),
    GKRAddress::BaseLayerWitness(36usize),
    GKRAddress::BaseLayerWitness(37usize),
    GKRAddress::BaseLayerWitness(38usize),
    GKRAddress::BaseLayerWitness(39usize),
    GKRAddress::BaseLayerWitness(42usize),
    GKRAddress::BaseLayerWitness(43usize),
    GKRAddress::BaseLayerWitness(44usize),
    GKRAddress::BaseLayerWitness(45usize),
    GKRAddress::BaseLayerWitness(46usize),
    GKRAddress::BaseLayerWitness(47usize),
    GKRAddress::BaseLayerWitness(48usize),
    GKRAddress::BaseLayerWitness(49usize),
    GKRAddress::BaseLayerWitness(50usize),
    GKRAddress::BaseLayerWitness(51usize),
    GKRAddress::BaseLayerWitness(52usize),
    GKRAddress::BaseLayerWitness(53usize),
    GKRAddress::BaseLayerWitness(54usize),
    GKRAddress::BaseLayerWitness(55usize),
    GKRAddress::BaseLayerWitness(56usize),
    GKRAddress::BaseLayerMemory(6usize),
    GKRAddress::BaseLayerMemory(7usize),
    GKRAddress::BaseLayerMemory(9usize),
    GKRAddress::BaseLayerMemory(10usize),
    GKRAddress::BaseLayerMemory(13usize),
    GKRAddress::BaseLayerMemory(14usize),
    GKRAddress::BaseLayerMemory(16usize),
    GKRAddress::BaseLayerMemory(17usize),
    GKRAddress::BaseLayerMemory(20usize),
    GKRAddress::BaseLayerMemory(21usize),
    GKRAddress::BaseLayerMemory(23usize),
    GKRAddress::BaseLayerMemory(24usize),
    GKRAddress::BaseLayerMemory(30usize),
    GKRAddress::BaseLayerMemory(31usize),
    GKRAddress::BaseLayerMemory(38usize),
    GKRAddress::BaseLayerMemory(39usize),
    GKRAddress::BaseLayerMemory(43usize),
    GKRAddress::BaseLayerMemory(44usize),
    GKRAddress::BaseLayerMemory(49usize),
    GKRAddress::BaseLayerMemory(51usize),
    GKRAddress::BaseLayerMemory(52usize),
    GKRAddress::BaseLayerMemory(53usize),
    GKRAddress::BaseLayerMemory(54usize),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
    GKRAddress::Cached {
        layer: 0usize,
        offset: 0usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 1usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 2usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 3usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 4usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 5usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 6usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 7usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 8usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 9usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 10usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 11usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 12usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 13usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 14usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 15usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 16usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 17usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 18usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 19usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 20usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 21usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 22usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 23usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 24usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 25usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 26usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 27usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 28usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 29usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 30usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 31usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 32usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 33usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 34usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 35usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 36usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 37usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 38usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 39usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 40usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 41usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 42usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 43usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 44usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 45usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 46usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 47usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 48usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 49usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 50usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 51usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 52usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 53usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 54usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 55usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 56usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 57usize,
    },
];
pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[];
pub const WHIR_FOLD_STEPS: [usize; 5usize] = [1usize, 5usize, 5usize, 5usize, 5usize];
pub const WHIR_QUERIES: [usize; 5usize] = [63usize, 11usize, 6usize, 4usize, 3usize];
pub const WHIR_POW_BITS: [u32; 5usize] = [28u32, 20u32, 14u32, 20u32, 23u32];
pub const MAX_POW_ENTRIES: usize = 88usize;
pub const FINAL_MONOMIALS_LEN: usize = 2usize;
pub const NUM_ORACLES: usize = 3usize;
pub const ORACLE_NUM_COLS: [usize; 3usize] = [55usize, 57usize, 9usize];
pub const ORACLE_DEPTHS: [usize; 3usize] = [18usize, 18usize, 18usize];
pub const TOTAL_ORACLE_COLS: usize = 121usize;
pub const WHIR_ORACLE_DEPTHS: [usize; 4usize] = [18usize, 18usize, 17usize, 16usize];
pub const WHIR_CAP_WORDS: usize = 128usize;
pub const INITIAL_WHIR_CLAIM_INDICES: [usize; 121usize] = [
    57usize, 58usize, 59usize, 60usize, 61usize, 62usize, 63usize, 64usize, 65usize, 66usize,
    67usize, 68usize, 69usize, 70usize, 71usize, 72usize, 73usize, 74usize, 75usize, 76usize,
    77usize, 78usize, 79usize, 80usize, 81usize, 82usize, 83usize, 84usize, 85usize, 86usize,
    87usize, 88usize, 89usize, 90usize, 91usize, 92usize, 93usize, 94usize, 95usize, 96usize,
    97usize, 98usize, 99usize, 100usize, 101usize, 102usize, 103usize, 104usize, 105usize,
    106usize, 107usize, 108usize, 109usize, 110usize, 111usize, 0usize, 1usize, 2usize, 3usize,
    4usize, 5usize, 6usize, 7usize, 8usize, 9usize, 10usize, 11usize, 12usize, 13usize, 14usize,
    15usize, 16usize, 17usize, 18usize, 19usize, 20usize, 21usize, 22usize, 23usize, 24usize,
    25usize, 26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize, 33usize, 34usize,
    35usize, 36usize, 37usize, 38usize, 39usize, 40usize, 41usize, 42usize, 43usize, 44usize,
    45usize, 46usize, 47usize, 48usize, 49usize, 50usize, 51usize, 52usize, 53usize, 54usize,
    55usize, 56usize, 112usize, 113usize, 114usize, 115usize, 116usize, 117usize, 118usize,
    119usize, 120usize,
];
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
    ::verifier_common::GKRVerifierOutput<'static, BabyBearExt4, GKR_ROUNDS, GKR_ADDRS>;
pub type ConcreteVerifierOutput = ::verifier_common::VerifierOutput<
    BabyBearExt4,
    INIT_AND_TEARDOWN_SETS,
    CAP_SIZE,
    NUM_MEMORY_COMMITS,
    NUM_SETUP_COMMITS,
>;
