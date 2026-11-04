use super::*;
use common_constants::keccak_special5::*;

#[derive(Clone, Copy, Debug)]
pub struct KeccakSpecial5AbiDescription;

impl DelegationAbiDescription for KeccakSpecial5AbiDescription {
    const DELEGATION_TYPE: u16 = KECCAK_SPECIAL5_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = KECCAK_SPECIAL5_BASE_ABI_REGISTER as usize;
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
        0..0, // x10
        0..0, // x11
        0..0, // x12
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
        0..0,                              // x10
        0..KECCAK_SPECIAL5_X11_NUM_WRITES, // x11
        0..0,                              // x12
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

    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16] = &[0; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS];
}

pub type KeccakSpecial5DelegationWitness = DelegationWitness<
    NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES,
    NUM_KECCAK_SPECIAL5_INDIRECT_READS,
    KECCAK_SPECIAL5_X11_NUM_WRITES,
    KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS,
>;
