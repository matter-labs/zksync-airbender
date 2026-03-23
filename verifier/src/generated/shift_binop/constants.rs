use verifier_common::cs::definitions::GKRAddress;
pub const GKR_ROUNDS: usize = 24usize;
pub const GKR_ADDRS: usize = 86usize;
pub const GKR_EVALS: usize = 128usize;
pub const GKR_TRANSCRIPT_U32: usize = 540usize;
pub const GKR_MAX_POW: usize = 12usize;
pub const GKR_EVAL_BUF: usize = 1392usize;
pub const GKR_COMMIT_BUF: usize = 32usize;
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
    GKRAddress::BaseLayerMemory(2usize),
    GKRAddress::BaseLayerMemory(3usize),
    GKRAddress::BaseLayerMemory(4usize),
    GKRAddress::BaseLayerMemory(5usize),
    GKRAddress::BaseLayerMemory(9usize),
    GKRAddress::BaseLayerMemory(10usize),
    GKRAddress::BaseLayerMemory(11usize),
    GKRAddress::BaseLayerMemory(12usize),
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
    GKRAddress::BaseLayerMemory(29usize),
    GKRAddress::Setup(0usize),
    GKRAddress::Setup(1usize),
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
];
pub const BASE_LAYER_ADDITIONAL_OPENINGS: &[GKRAddress] = &[
    GKRAddress::BaseLayerWitness(0usize),
    GKRAddress::BaseLayerWitness(1usize),
    GKRAddress::BaseLayerWitness(2usize),
    GKRAddress::BaseLayerWitness(5usize),
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
    GKRAddress::Setup(2usize),
    GKRAddress::Setup(3usize),
    GKRAddress::Setup(4usize),
    GKRAddress::Setup(5usize),
    GKRAddress::Setup(6usize),
    GKRAddress::Setup(7usize),
    GKRAddress::Setup(8usize),
    GKRAddress::Setup(9usize),
    GKRAddress::Setup(10usize),
    GKRAddress::Setup(11usize),
];
pub const TRACE_LEN_LOG2: usize = 24usize;
pub const WHIR_ROUNDS: usize = 6usize;
pub const WHIR_FOLD_STEPS: [usize; 6usize] = [1usize, 4usize, 4usize, 4usize, 4usize, 4usize];
pub const WHIR_QUERIES: [usize; 6usize] = [68usize, 23usize, 12usize, 10usize, 10usize, 10usize];
pub const WHIR_POW_BITS: [u32; 6usize] = [24u32, 24u32, 24u32, 24u32, 24u32, 24u32];
pub const WHIR_BASE_LDE_FACTOR: usize = 2usize;
pub const WHIR_LDE_FACTORS: [usize; 5usize] = [8usize, 64usize, 128usize, 128usize, 128usize];
pub const WHIR_CAP_SIZE: usize = 16usize;
pub const FINAL_M: usize = 3usize;
pub const FINAL_MONOMIALS_LEN: usize = 8usize;
pub const NUM_BASE_CLAIMS: usize = 49usize;
pub const NUM_MEMORY_CLAIMS: usize = 19usize;
pub const NUM_WITNESS_CLAIMS: usize = 28usize;
pub const NUM_SETUP_CLAIMS: usize = 2usize;
pub const BASE_ORACLE_DEPTH: usize = 20usize;
pub const WHIR_ORACLE_DEPTHS: [usize; 5usize] = [18usize, 17usize, 14usize, 10usize, 6usize];
