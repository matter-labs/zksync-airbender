use verifier_common::cs::definitions::{GKRAddress, VirtualSetupPoly};
pub const GKR_ROUNDS: usize = 24usize;
pub const GKR_ADDRS: usize = 66usize;
pub const GKR_EVALS: usize = 128usize;
pub const GKR_TRANSCRIPT_U32: usize = 540usize;
pub const GKR_MAX_POW: usize = 1usize;
pub const GKR_EVAL_BUF: usize = 1072usize;
pub const GKR_COMMIT_BUF: usize = 32usize;
pub const GKR_EVALS_COMMIT_BUF: usize = 528usize;
pub const DRAW_BUF_CAPACITY: usize = 24usize;
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
    GKRAddress::BaseLayerMemory(0usize),
    GKRAddress::BaseLayerMemory(1usize),
    GKRAddress::BaseLayerMemory(2usize),
    GKRAddress::BaseLayerMemory(3usize),
    GKRAddress::BaseLayerMemory(4usize),
    GKRAddress::BaseLayerMemory(5usize),
    GKRAddress::BaseLayerMemory(6usize),
    GKRAddress::BaseLayerMemory(7usize),
    GKRAddress::BaseLayerMemory(8usize),
    GKRAddress::BaseLayerMemory(9usize),
    GKRAddress::BaseLayerMemory(10usize),
    GKRAddress::BaseLayerMemory(11usize),
    GKRAddress::BaseLayerMemory(12usize),
    GKRAddress::BaseLayerMemory(13usize),
    GKRAddress::BaseLayerMemory(14usize),
    GKRAddress::BaseLayerMemory(15usize),
    GKRAddress::BaseLayerMemory(16usize),
    GKRAddress::BaseLayerMemory(17usize),
    GKRAddress::BaseLayerMemory(18usize),
    GKRAddress::BaseLayerMemory(19usize),
    GKRAddress::BaseLayerMemory(20usize),
    GKRAddress::BaseLayerMemory(21usize),
    GKRAddress::BaseLayerMemory(22usize),
    GKRAddress::BaseLayerMemory(23usize),
    GKRAddress::BaseLayerMemory(24usize),
    GKRAddress::BaseLayerMemory(25usize),
    GKRAddress::Setup(0usize),
    GKRAddress::Setup(1usize),
    GKRAddress::Setup(2usize),
    GKRAddress::Setup(3usize),
    GKRAddress::Setup(4usize),
    GKRAddress::Setup(5usize),
    GKRAddress::Setup(6usize),
    GKRAddress::Setup(7usize),
    GKRAddress::Setup(8usize),
    GKRAddress::Setup(9usize),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
];
pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[];
pub const WHIR_FOLD_STEPS: [usize; 6usize] = [1usize, 4usize, 4usize, 4usize, 4usize, 4usize];
pub const WHIR_QUERIES: [usize; 6usize] = [68usize, 23usize, 12usize, 10usize, 10usize, 10usize];
pub const WHIR_POW_BITS: [u32; 6usize] = [24u32, 24u32, 24u32, 24u32, 24u32, 24u32];
pub const MAX_POW_ENTRIES: usize = 128usize;
pub const FINAL_MONOMIALS_LEN: usize = 8usize;
pub const NUM_ORACLES: usize = 3usize;
pub const ORACLE_NUM_COLS: [usize; 3usize] = [26usize, 28usize, 10usize];
pub const ORACLE_CAP_WORDS: [usize; 3usize] = [128usize, 128usize, 256usize];
pub const ORACLE_DEPTHS: [usize; 3usize] = [20usize, 20usize, 19usize];
pub const TOTAL_ORACLE_COLS: usize = 64usize;
pub const TOTAL_CAP_WORDS: usize = 512usize;
pub const ORACLE_CAP_TRANSCRIPT_OFFSETS: [usize; 3usize] = [256usize, 384usize, 0usize];
pub const WHIR_ORACLE_DEPTHS: [usize; 5usize] = [18usize, 17usize, 14usize, 10usize, 6usize];
pub const WHIR_CAP_WORDS: usize = 128usize;
pub const CAPS_OFFSET_IN_TRANSCRIPT: usize = 28usize;
pub const INITIAL_WHIR_CLAIM_INDICES: [usize; 64usize] = [
    28usize, 29usize, 30usize, 31usize, 32usize, 33usize, 34usize, 35usize, 36usize, 37usize,
    38usize, 39usize, 40usize, 41usize, 42usize, 43usize, 44usize, 45usize, 46usize, 47usize,
    48usize, 49usize, 50usize, 51usize, 52usize, 53usize, 0usize, 1usize, 2usize, 3usize, 4usize,
    5usize, 6usize, 7usize, 8usize, 9usize, 10usize, 11usize, 12usize, 13usize, 14usize, 15usize,
    16usize, 17usize, 18usize, 19usize, 20usize, 21usize, 22usize, 23usize, 24usize, 25usize,
    26usize, 27usize, 54usize, 55usize, 56usize, 57usize, 58usize, 59usize, 60usize, 61usize,
    62usize, 63usize,
];
