use super::*;
use common_constants::blake2s_g_function::*;

#[derive(Clone, Copy, Debug)]
pub struct Blake2sGFunctionAbiDescription;

impl DelegationAbiDescription for Blake2sGFunctionAbiDescription {
    const DELEGATION_TYPE: u16 = BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = BLAKE2S_G_FUNCTION_BASE_ABI_REGISTER as usize;
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
        0..0,                                // x10
        0..BLAKE2S_G_FUNCTION_X11_NUM_READS, // x11
        0..0,                                // x12
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
        0..BLAKE2S_G_FUNCTION_X10_NUM_WRITES, // x10
        0..0,                                 // x11
        0..0,                                 // x12
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

    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16] =
        &[0; NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS];

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

pub type Blake2sGFunctionDelegationWitness = DelegationWitness<
    NUM_BLAKE2S_G_FUNCTION_REGISTER_ACCESSES,
    BLAKE2S_G_FUNCTION_X11_NUM_READS,
    BLAKE2S_G_FUNCTION_X10_NUM_WRITES,
    NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS,
>;
