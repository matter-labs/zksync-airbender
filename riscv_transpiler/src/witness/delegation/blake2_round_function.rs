use super::*;
use common_constants::blake2s_with_control::*;

#[derive(Clone, Copy, Debug)]
pub struct Blake2sRoundFunctionAbiDescription;

impl DelegationAbiDescription for Blake2sRoundFunctionAbiDescription {
    const DELEGATION_TYPE: u16 = BLAKE2S_DELEGATION_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = BLAKE2S_BASE_ABI_REGISTER as usize;
    const INDIRECT_READS_DESCRIPTION: &'static [Range<usize>; 32] = &[
        0..0, // x0
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,                     // x10
        0..BLAKE2S_X11_NUM_READS, // x11
        0..0,                     // x12
        0..0,
        0..0,
        0..0,
        0..0, // x16
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
    ];

    const INDIRECT_WRITES_DESCRIPTION: &'static [Range<usize>; 32] = &[
        0..0, // x0
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..BLAKE2S_X10_NUM_WRITES, // x10
        0..0,                      // x11
        0..0,                      // x12
        0..0,
        0..0,
        0..0,
        0..0, // x16
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
        0..0,
    ];

    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16] = &[];

    // const VARIABLE_OFFSETS_DESCRIPTION: &'static [Range<usize>; 32] = &[
    //     0..0, // x0
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0, // x10
    //     0..0, // x11
    //     0..0, // x12
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0, // x16
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    //     0..0,
    // ];
}

pub type Blake2sRoundFunctionDelegationWitness = DelegationWitness<
    NUM_BLAKE2S_REGISTER_ACCESSES,
    BLAKE2S_X11_NUM_READS,
    BLAKE2S_X10_NUM_WRITES,
    NUM_BLAKE2S_VARIABLE_OFFSETS,
>;
