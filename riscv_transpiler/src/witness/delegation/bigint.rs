use super::*;
use common_constants::bigint_with_control::*;

#[derive(Clone, Copy, Debug)]
pub struct BigintAbiDescription;

impl DelegationAbiDescription for BigintAbiDescription {
    const DELEGATION_TYPE: u16 = BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16;
    const BASE_REGISTER: usize = BIGINT_BASE_ABI_REGISTER as usize;
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
        0..0,                    // x10
        0..BIGINT_X11_NUM_READS, // x11
        0..0,                    // x12
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
        0..BIGINT_X10_NUM_WRITES, // x10
        0..0,                     // x11
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

pub type BigintDelegationWitness = DelegationWitness<
    NUM_BIGINT_REGISTER_ACCESSES,
    BIGINT_X11_NUM_READS,
    BIGINT_X10_NUM_WRITES,
    NUM_BIGINT_VARIABLE_OFFSETS,
>;
