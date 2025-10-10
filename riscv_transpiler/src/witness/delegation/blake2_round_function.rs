use super::*;

#[derive(Clone, Copy, Debug)]
pub struct Blake2sRoundFunctionAbiDescription;

impl DelegationAbiDescription for Blake2sRoundFunctionAbiDescription {
    const DELEGATION_TYPE: u16 =
        common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16;
    const BASE_REGISTER: usize =
        common_constants::blake2s_with_control::BLAKE2S_BASE_ABI_REGISTER as usize;
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
        0..0,  // x10
        0..16, // x11
        0..0,  // x12
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
        0..24, // x10
        0..0,  // x11
        0..0,  // x12
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

pub type Blake2sRoundFunctionDelegationWitness = DelegationWitness<4, 16, 24, 0>;
