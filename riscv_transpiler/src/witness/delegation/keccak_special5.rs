use common_constants::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS;

use super::*;

#[derive(Clone, Copy, Debug)]
pub struct KeccakSpecial5AbiDescription;

impl DelegationAbiDescription for KeccakSpecial5AbiDescription {
    const DELEGATION_TYPE: u16 =
        common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16;
    const BASE_REGISTER: usize =
        common_constants::keccak_special5::KECCAK_SPECIAL5_BASE_ABI_REGISTER as usize;
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
        0..0, // x10
        0..0, // x11 SHOULD WE PUT DUMMIES HERE?
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

    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16] = &[0; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS];
}

pub type KeccakSpecial5DelegationWitness = DelegationWitness<
    2,
    0,
    { KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS * 2 },
    KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS,
>;
