use super::*;

#[derive(Clone, Copy, Debug)]
pub struct BigintAbiDescription;

impl DelegationAbiDescription for BigintAbiDescription {
    const DELEGATION_TYPE: u16 =
        common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16;
    const BASE_REGISTER: usize =
        common_constants::bigint_with_control::BIGINT_BASE_ABI_REGISTER as usize;
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
        0..8, // x11
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
        0..8, // x10
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

pub type BigintDelegationWitness = DelegationWitness<3, 8, 8, 0>;
