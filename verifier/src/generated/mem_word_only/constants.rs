use verifier_common::cs::definitions::{GKRAddress, VirtualSetupPoly};
pub const GKR_ROUNDS: usize = 24usize;
pub const GKR_ADDRS: usize = 51usize;
pub const GKR_EVALS: usize = 128usize;
pub const GKR_TRANSCRIPT_U32: usize = 540usize;
pub const GKR_MAX_POW: usize = 1usize;
pub const GKR_EVAL_BUF: usize = 832usize;
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
    GKRAddress::BaseLayerMemory(26usize),
    GKRAddress::BaseLayerMemory(27usize),
    GKRAddress::BaseLayerMemory(28usize),
    GKRAddress::Setup(0usize),
    GKRAddress::Setup(1usize),
    GKRAddress::Setup(2usize),
    GKRAddress::Setup(3usize),
    GKRAddress::Setup(4usize),
    GKRAddress::Setup(5usize),
    GKRAddress::Setup(6usize),
    GKRAddress::Setup(7usize),
    GKRAddress::Setup(8usize),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
    GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
];
pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[];
pub const WHIR_FOLD_STEPS: [usize; 6usize] = [1usize, 4usize, 4usize, 4usize, 4usize, 4usize];
pub const WHIR_QUERIES: [usize; 6usize] = [68usize, 23usize, 12usize, 10usize, 10usize, 10usize];
pub const WHIR_POW_BITS: [u32; 6usize] = [24u32, 24u32, 24u32, 24u32, 24u32, 24u32];
pub const FINAL_MONOMIALS_LEN: usize = 8usize;
pub const NUM_ORACLES: usize = 3usize;
pub const ORACLE_NUM_COLS: [usize; 3usize] = [29usize, 11usize, 9usize];
pub const ORACLE_CAP_WORDS: [usize; 3usize] = [128usize, 128usize, 256usize];
pub const ORACLE_DEPTHS: [usize; 3usize] = [20usize, 20usize, 19usize];
pub const TOTAL_ORACLE_COLS: usize = 49usize;
pub const TOTAL_CAP_WORDS: usize = 512usize;
pub const ORACLE_CAP_TRANSCRIPT_OFFSETS: [usize; 3usize] = [256usize, 384usize, 0usize];
pub const WHIR_ORACLE_DEPTHS: [usize; 5usize] = [18usize, 17usize, 14usize, 10usize, 6usize];
pub const WHIR_CAP_WORDS: usize = 128usize;
pub const CAPS_OFFSET_IN_TRANSCRIPT: usize = 28usize;
