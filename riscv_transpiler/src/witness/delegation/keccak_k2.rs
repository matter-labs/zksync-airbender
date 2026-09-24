use super::*;
use common_constants::keccak_k2::*;

#[derive(Clone, Copy, Debug)]
pub struct KeccakColumnParityAbiDescription;

impl DelegationAbiDescription for KeccakColumnParityAbiDescription {
    const DELEGATION_TYPE: u16 = KECCAK_COLUMN_PARITY_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = KECCAK_K2_BASE_ABI_REGISTER as usize;
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
        0..0,                                   // x10
        0..KECCAK_COLUMN_PARITY_X11_NUM_WRITES, // x11
        0..0,                                   // x12
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
        &[0; KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS];
}

pub type KeccakColumnParityDelegationWitness = DelegationWitness<
    NUM_KECCAK_K2_REGISTER_ACCESSES,
    NUM_KECCAK_K2_INDIRECT_READS,
    KECCAK_COLUMN_PARITY_X11_NUM_WRITES,
    KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
>;

#[derive(Clone, Copy, Debug)]
pub struct KeccakThetaRhoAbiDescription;

impl DelegationAbiDescription for KeccakThetaRhoAbiDescription {
    const DELEGATION_TYPE: u16 = KECCAK_THETA_RHO_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = KECCAK_K2_BASE_ABI_REGISTER as usize;
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
        0..0,                               // x10
        0..KECCAK_THETA_RHO_X11_NUM_WRITES, // x11
        0..0,                               // x12
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
        &[0; KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS];
}

pub type KeccakThetaRhoDelegationWitness = DelegationWitness<
    NUM_KECCAK_K2_REGISTER_ACCESSES,
    NUM_KECCAK_K2_INDIRECT_READS,
    KECCAK_THETA_RHO_X11_NUM_WRITES,
    KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
>;

#[derive(Clone, Copy, Debug)]
pub struct KeccakChi5AbiDescription;

impl DelegationAbiDescription for KeccakChi5AbiDescription {
    const DELEGATION_TYPE: u16 = KECCAK_CHI5_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = KECCAK_K2_BASE_ABI_REGISTER as usize;
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
        0..0,                          // x10
        0..KECCAK_CHI5_X11_NUM_WRITES, // x11
        0..0,                          // x12
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

    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16] = &[0; KECCAK_CHI5_NUM_VARIABLE_OFFSETS];
}

pub type KeccakChi5DelegationWitness = DelegationWitness<
    NUM_KECCAK_K2_REGISTER_ACCESSES,
    NUM_KECCAK_K2_INDIRECT_READS,
    KECCAK_CHI5_X11_NUM_WRITES,
    KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
>;
