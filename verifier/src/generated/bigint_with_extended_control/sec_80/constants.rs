use super::common::EXT_DEGREE;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::cs::definitions::{GKRAddress, VirtualSetupPoly};
use verifier_common::{DIM_REDUCE_EVAL_POINTS, STANDARD_EVAL_POINTS, SUMCHECK_POLY_COEFFS};
pub const GKR_ROUNDS: usize = 22usize;
pub const GKR_ADDRS: usize = 403usize;
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
pub const GKR_MAX_POW: usize = 1usize;
pub const GKR_EVAL_BUF: usize = {
    let dim_reducing = 403usize * DIM_REDUCE_EVAL_POINTS * EXT_DEGREE;
    let standard = 403usize * STANDARD_EVAL_POINTS * EXT_DEGREE;
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
pub const DRAW_BUF_CAPACITY: usize =
    (5usize * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
pub const LAYER_0_SORTED_ADDRS: &[GKRAddress] = &[
    GKRAddress::BaseLayerWitness(0usize),
    GKRAddress::BaseLayerWitness(1usize),
    GKRAddress::BaseLayerWitness(2usize),
    GKRAddress::BaseLayerWitness(3usize),
    GKRAddress::BaseLayerWitness(4usize),
    GKRAddress::BaseLayerWitness(5usize),
    GKRAddress::BaseLayerWitness(6usize),
    GKRAddress::BaseLayerWitness(7usize),
    GKRAddress::BaseLayerWitness(8usize),
    GKRAddress::BaseLayerWitness(9usize),
    GKRAddress::BaseLayerWitness(10usize),
    GKRAddress::BaseLayerWitness(11usize),
    GKRAddress::BaseLayerWitness(12usize),
    GKRAddress::BaseLayerWitness(13usize),
    GKRAddress::BaseLayerWitness(14usize),
    GKRAddress::BaseLayerWitness(15usize),
    GKRAddress::BaseLayerWitness(16usize),
    GKRAddress::BaseLayerWitness(17usize),
    GKRAddress::BaseLayerWitness(18usize),
    GKRAddress::BaseLayerWitness(19usize),
    GKRAddress::BaseLayerWitness(20usize),
    GKRAddress::BaseLayerWitness(21usize),
    GKRAddress::BaseLayerWitness(22usize),
    GKRAddress::BaseLayerWitness(23usize),
    GKRAddress::BaseLayerWitness(24usize),
    GKRAddress::BaseLayerWitness(25usize),
    GKRAddress::BaseLayerWitness(26usize),
    GKRAddress::BaseLayerWitness(27usize),
    GKRAddress::BaseLayerWitness(28usize),
    GKRAddress::BaseLayerWitness(29usize),
    GKRAddress::BaseLayerWitness(30usize),
    GKRAddress::BaseLayerWitness(31usize),
    GKRAddress::BaseLayerWitness(32usize),
    GKRAddress::BaseLayerWitness(33usize),
    GKRAddress::BaseLayerWitness(34usize),
    GKRAddress::BaseLayerWitness(35usize),
    GKRAddress::BaseLayerWitness(36usize),
    GKRAddress::BaseLayerWitness(37usize),
    GKRAddress::BaseLayerWitness(38usize),
    GKRAddress::BaseLayerWitness(39usize),
    GKRAddress::BaseLayerWitness(40usize),
    GKRAddress::BaseLayerWitness(41usize),
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
    GKRAddress::BaseLayerWitness(57usize),
    GKRAddress::BaseLayerWitness(58usize),
    GKRAddress::BaseLayerWitness(59usize),
    GKRAddress::BaseLayerWitness(60usize),
    GKRAddress::BaseLayerWitness(61usize),
    GKRAddress::BaseLayerWitness(62usize),
    GKRAddress::BaseLayerWitness(63usize),
    GKRAddress::BaseLayerWitness(64usize),
    GKRAddress::BaseLayerWitness(65usize),
    GKRAddress::BaseLayerWitness(66usize),
    GKRAddress::BaseLayerWitness(67usize),
    GKRAddress::BaseLayerWitness(68usize),
    GKRAddress::BaseLayerWitness(69usize),
    GKRAddress::BaseLayerWitness(70usize),
    GKRAddress::BaseLayerWitness(71usize),
    GKRAddress::BaseLayerWitness(72usize),
    GKRAddress::BaseLayerWitness(73usize),
    GKRAddress::BaseLayerWitness(74usize),
    GKRAddress::BaseLayerWitness(75usize),
    GKRAddress::BaseLayerWitness(76usize),
    GKRAddress::BaseLayerWitness(77usize),
    GKRAddress::BaseLayerWitness(78usize),
    GKRAddress::BaseLayerWitness(79usize),
    GKRAddress::BaseLayerWitness(80usize),
    GKRAddress::BaseLayerWitness(81usize),
    GKRAddress::BaseLayerWitness(82usize),
    GKRAddress::BaseLayerWitness(83usize),
    GKRAddress::BaseLayerWitness(84usize),
    GKRAddress::BaseLayerWitness(85usize),
    GKRAddress::BaseLayerWitness(86usize),
    GKRAddress::BaseLayerWitness(87usize),
    GKRAddress::BaseLayerWitness(88usize),
    GKRAddress::BaseLayerWitness(89usize),
    GKRAddress::BaseLayerWitness(90usize),
    GKRAddress::BaseLayerWitness(91usize),
    GKRAddress::BaseLayerWitness(92usize),
    GKRAddress::BaseLayerWitness(93usize),
    GKRAddress::BaseLayerWitness(94usize),
    GKRAddress::BaseLayerWitness(95usize),
    GKRAddress::BaseLayerWitness(96usize),
    GKRAddress::BaseLayerWitness(97usize),
    GKRAddress::BaseLayerWitness(98usize),
    GKRAddress::BaseLayerWitness(99usize),
    GKRAddress::BaseLayerWitness(100usize),
    GKRAddress::BaseLayerWitness(101usize),
    GKRAddress::BaseLayerWitness(102usize),
    GKRAddress::BaseLayerWitness(103usize),
    GKRAddress::BaseLayerWitness(104usize),
    GKRAddress::BaseLayerWitness(105usize),
    GKRAddress::BaseLayerWitness(106usize),
    GKRAddress::BaseLayerWitness(107usize),
    GKRAddress::BaseLayerWitness(108usize),
    GKRAddress::BaseLayerWitness(109usize),
    GKRAddress::BaseLayerWitness(110usize),
    GKRAddress::BaseLayerWitness(111usize),
    GKRAddress::BaseLayerWitness(112usize),
    GKRAddress::BaseLayerWitness(113usize),
    GKRAddress::BaseLayerWitness(114usize),
    GKRAddress::BaseLayerWitness(115usize),
    GKRAddress::BaseLayerWitness(116usize),
    GKRAddress::BaseLayerWitness(117usize),
    GKRAddress::BaseLayerWitness(118usize),
    GKRAddress::BaseLayerWitness(119usize),
    GKRAddress::BaseLayerWitness(120usize),
    GKRAddress::BaseLayerWitness(121usize),
    GKRAddress::BaseLayerWitness(122usize),
    GKRAddress::BaseLayerWitness(123usize),
    GKRAddress::BaseLayerWitness(124usize),
    GKRAddress::BaseLayerWitness(125usize),
    GKRAddress::BaseLayerWitness(126usize),
    GKRAddress::BaseLayerWitness(127usize),
    GKRAddress::BaseLayerWitness(128usize),
    GKRAddress::BaseLayerWitness(129usize),
    GKRAddress::BaseLayerWitness(130usize),
    GKRAddress::BaseLayerWitness(131usize),
    GKRAddress::BaseLayerWitness(132usize),
    GKRAddress::BaseLayerWitness(133usize),
    GKRAddress::BaseLayerWitness(134usize),
    GKRAddress::BaseLayerWitness(135usize),
    GKRAddress::BaseLayerWitness(136usize),
    GKRAddress::BaseLayerWitness(137usize),
    GKRAddress::BaseLayerWitness(138usize),
    GKRAddress::BaseLayerWitness(139usize),
    GKRAddress::BaseLayerWitness(140usize),
    GKRAddress::BaseLayerWitness(141usize),
    GKRAddress::BaseLayerWitness(142usize),
    GKRAddress::BaseLayerWitness(143usize),
    GKRAddress::BaseLayerWitness(144usize),
    GKRAddress::BaseLayerWitness(145usize),
    GKRAddress::BaseLayerWitness(146usize),
    GKRAddress::BaseLayerWitness(147usize),
    GKRAddress::BaseLayerWitness(148usize),
    GKRAddress::BaseLayerWitness(149usize),
    GKRAddress::BaseLayerWitness(150usize),
    GKRAddress::BaseLayerWitness(151usize),
    GKRAddress::BaseLayerWitness(152usize),
    GKRAddress::BaseLayerWitness(153usize),
    GKRAddress::BaseLayerWitness(154usize),
    GKRAddress::BaseLayerWitness(155usize),
    GKRAddress::BaseLayerWitness(156usize),
    GKRAddress::BaseLayerWitness(157usize),
    GKRAddress::BaseLayerWitness(158usize),
    GKRAddress::BaseLayerWitness(159usize),
    GKRAddress::BaseLayerWitness(160usize),
    GKRAddress::BaseLayerMemory(6usize),
    GKRAddress::BaseLayerMemory(7usize),
    GKRAddress::BaseLayerMemory(8usize),
    GKRAddress::BaseLayerMemory(9usize),
    GKRAddress::BaseLayerMemory(12usize),
    GKRAddress::BaseLayerMemory(13usize),
    GKRAddress::BaseLayerMemory(14usize),
    GKRAddress::BaseLayerMemory(15usize),
    GKRAddress::BaseLayerMemory(18usize),
    GKRAddress::BaseLayerMemory(19usize),
    GKRAddress::BaseLayerMemory(20usize),
    GKRAddress::BaseLayerMemory(21usize),
    GKRAddress::BaseLayerMemory(24usize),
    GKRAddress::BaseLayerMemory(25usize),
    GKRAddress::BaseLayerMemory(26usize),
    GKRAddress::BaseLayerMemory(27usize),
    GKRAddress::BaseLayerMemory(30usize),
    GKRAddress::BaseLayerMemory(31usize),
    GKRAddress::BaseLayerMemory(32usize),
    GKRAddress::BaseLayerMemory(33usize),
    GKRAddress::BaseLayerMemory(36usize),
    GKRAddress::BaseLayerMemory(37usize),
    GKRAddress::BaseLayerMemory(38usize),
    GKRAddress::BaseLayerMemory(39usize),
    GKRAddress::BaseLayerMemory(42usize),
    GKRAddress::BaseLayerMemory(43usize),
    GKRAddress::BaseLayerMemory(44usize),
    GKRAddress::BaseLayerMemory(45usize),
    GKRAddress::BaseLayerMemory(48usize),
    GKRAddress::BaseLayerMemory(49usize),
    GKRAddress::BaseLayerMemory(50usize),
    GKRAddress::BaseLayerMemory(51usize),
    GKRAddress::BaseLayerMemory(58usize),
    GKRAddress::BaseLayerMemory(59usize),
    GKRAddress::BaseLayerMemory(62usize),
    GKRAddress::BaseLayerMemory(63usize),
    GKRAddress::BaseLayerMemory(66usize),
    GKRAddress::BaseLayerMemory(67usize),
    GKRAddress::BaseLayerMemory(70usize),
    GKRAddress::BaseLayerMemory(71usize),
    GKRAddress::BaseLayerMemory(74usize),
    GKRAddress::BaseLayerMemory(75usize),
    GKRAddress::BaseLayerMemory(78usize),
    GKRAddress::BaseLayerMemory(79usize),
    GKRAddress::BaseLayerMemory(82usize),
    GKRAddress::BaseLayerMemory(83usize),
    GKRAddress::BaseLayerMemory(86usize),
    GKRAddress::BaseLayerMemory(87usize),
    GKRAddress::BaseLayerMemory(90usize),
    GKRAddress::BaseLayerMemory(92usize),
    GKRAddress::BaseLayerMemory(93usize),
    GKRAddress::BaseLayerMemory(94usize),
    GKRAddress::BaseLayerMemory(95usize),
    GKRAddress::BaseLayerMemory(96usize),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
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
    GKRAddress::Cached {
        layer: 0usize,
        offset: 58usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 59usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 60usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 61usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 62usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 63usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 64usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 65usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 66usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 67usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 68usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 69usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 70usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 71usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 72usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 73usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 74usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 75usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 76usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 77usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 78usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 79usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 80usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 81usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 82usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 83usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 84usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 85usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 86usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 87usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 88usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 89usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 90usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 91usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 92usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 93usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 94usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 95usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 96usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 97usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 98usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 99usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 100usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 101usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 102usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 103usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 104usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 105usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 106usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 107usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 108usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 109usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 110usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 111usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 112usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 113usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 114usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 115usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 116usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 117usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 118usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 119usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 120usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 121usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 122usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 123usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 124usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 125usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 126usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 127usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 128usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 129usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 130usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 131usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 132usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 133usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 134usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 135usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 136usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 137usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 138usize,
    },
    GKRAddress::Cached {
        layer: 0usize,
        offset: 139usize,
    },
];
pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[];
pub const WHIR_FOLD_STEPS: [usize; 5usize] = [1usize, 5usize, 5usize, 5usize, 5usize];
pub const WHIR_QUERIES: [usize; 5usize] = [63usize, 11usize, 6usize, 4usize, 3usize];
pub const WHIR_POW_BITS: [u32; 5usize] = [28u32, 20u32, 14u32, 20u32, 23u32];
pub const MAX_POW_ENTRIES: usize = 88usize;
pub const FINAL_MONOMIALS_LEN: usize = 2usize;
pub const NUM_ORACLES: usize = 3usize;
pub const ORACLE_NUM_COLS: [usize; 3usize] = [97usize, 161usize, 3usize];
pub const ORACLE_DEPTHS: [usize; 3usize] = [18usize, 18usize, 18usize];
pub const TOTAL_ORACLE_COLS: usize = 261usize;
pub const WHIR_ORACLE_DEPTHS: [usize; 4usize] = [18usize, 18usize, 17usize, 16usize];
pub const WHIR_CAP_WORDS: usize = 128usize;
pub const INITIAL_WHIR_CLAIM_INDICES: [usize; 261usize] = [
    161usize, 162usize, 163usize, 164usize, 165usize, 166usize, 167usize, 168usize, 169usize,
    170usize, 171usize, 172usize, 173usize, 174usize, 175usize, 176usize, 177usize, 178usize,
    179usize, 180usize, 181usize, 182usize, 183usize, 184usize, 185usize, 186usize, 187usize,
    188usize, 189usize, 190usize, 191usize, 192usize, 193usize, 194usize, 195usize, 196usize,
    197usize, 198usize, 199usize, 200usize, 201usize, 202usize, 203usize, 204usize, 205usize,
    206usize, 207usize, 208usize, 209usize, 210usize, 211usize, 212usize, 213usize, 214usize,
    215usize, 216usize, 217usize, 218usize, 219usize, 220usize, 221usize, 222usize, 223usize,
    224usize, 225usize, 226usize, 227usize, 228usize, 229usize, 230usize, 231usize, 232usize,
    233usize, 234usize, 235usize, 236usize, 237usize, 238usize, 239usize, 240usize, 241usize,
    242usize, 243usize, 244usize, 245usize, 246usize, 247usize, 248usize, 249usize, 250usize,
    251usize, 252usize, 253usize, 254usize, 255usize, 256usize, 257usize, 0usize, 1usize, 2usize,
    3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize, 10usize, 11usize, 12usize, 13usize,
    14usize, 15usize, 16usize, 17usize, 18usize, 19usize, 20usize, 21usize, 22usize, 23usize,
    24usize, 25usize, 26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize, 33usize,
    34usize, 35usize, 36usize, 37usize, 38usize, 39usize, 40usize, 41usize, 42usize, 43usize,
    44usize, 45usize, 46usize, 47usize, 48usize, 49usize, 50usize, 51usize, 52usize, 53usize,
    54usize, 55usize, 56usize, 57usize, 58usize, 59usize, 60usize, 61usize, 62usize, 63usize,
    64usize, 65usize, 66usize, 67usize, 68usize, 69usize, 70usize, 71usize, 72usize, 73usize,
    74usize, 75usize, 76usize, 77usize, 78usize, 79usize, 80usize, 81usize, 82usize, 83usize,
    84usize, 85usize, 86usize, 87usize, 88usize, 89usize, 90usize, 91usize, 92usize, 93usize,
    94usize, 95usize, 96usize, 97usize, 98usize, 99usize, 100usize, 101usize, 102usize, 103usize,
    104usize, 105usize, 106usize, 107usize, 108usize, 109usize, 110usize, 111usize, 112usize,
    113usize, 114usize, 115usize, 116usize, 117usize, 118usize, 119usize, 120usize, 121usize,
    122usize, 123usize, 124usize, 125usize, 126usize, 127usize, 128usize, 129usize, 130usize,
    131usize, 132usize, 133usize, 134usize, 135usize, 136usize, 137usize, 138usize, 139usize,
    140usize, 141usize, 142usize, 143usize, 144usize, 145usize, 146usize, 147usize, 148usize,
    149usize, 150usize, 151usize, 152usize, 153usize, 154usize, 155usize, 156usize, 157usize,
    158usize, 159usize, 160usize, 258usize, 259usize, 260usize,
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
