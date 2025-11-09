use common_constants::TimestampScalar;
use core::fmt::Debug;
use risc_v_simulator::abstractions::tracer::{
    RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData,
};
use std::ops::Range;

pub mod bigint;
pub mod blake2_round_function;
pub mod keccak_special5;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DelegationWitness<
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
> {
    pub write_timestamp: TimestampScalar,
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(
        deserialize = "[RegisterOrIndirectReadWriteData; REG_ACCESSES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[RegisterOrIndirectReadWriteData; REG_ACCESSES]: serde::Serialize"
    ))]
    pub reg_accesses: [RegisterOrIndirectReadWriteData; REG_ACCESSES],
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(
        deserialize = "[RegisterOrIndirectReadData; INDIRECT_READS]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(serialize = "[RegisterOrIndirectReadData; INDIRECT_READS]: serde::Serialize"))]
    pub indirect_reads: [RegisterOrIndirectReadData; INDIRECT_READS],
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(
        deserialize = "[RegisterOrIndirectReadWriteData; INDIRECT_WRITES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[RegisterOrIndirectReadWriteData; INDIRECT_WRITES]: serde::Serialize"
    ))]
    pub indirect_writes: [RegisterOrIndirectReadWriteData; INDIRECT_WRITES],
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(deserialize = "[u16; VARIABLE_OFFSETS]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[u16; VARIABLE_OFFSETS]: serde::Serialize"))]
    pub variables_offsets: [u16; VARIABLE_OFFSETS],
}

impl<
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    > DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>
{
    pub fn empty() -> Self {
        Self {
            write_timestamp: 0,
            reg_accesses: [RegisterOrIndirectReadWriteData::EMPTY; REG_ACCESSES],
            indirect_reads: [RegisterOrIndirectReadData::EMPTY; INDIRECT_READS],
            indirect_writes: [RegisterOrIndirectReadWriteData::EMPTY; INDIRECT_WRITES],
            variables_offsets: [0u16; VARIABLE_OFFSETS],
        }
    }
}

pub trait DelegationAbiDescription: 'static + Clone + Copy + Debug + Send + Sync {
    const DELEGATION_TYPE: u16;
    const BASE_REGISTER: usize;
    const INDIRECT_READS_DESCRIPTION: &'static [Range<usize>; 32];
    const INDIRECT_WRITES_DESCRIPTION: &'static [Range<usize>; 32];
    const VARIABLE_OFFSETS_DESCRIPTION: &'static [u16];
    // const VARIABLE_OFFSETS_DESCRIPTION: &'static [Range<usize>; 32];

    fn use_read_indirects(reg_idx: usize) -> bool {
        if Self::INDIRECT_READS_DESCRIPTION[reg_idx].is_empty() {
            debug_assert!(Self::INDIRECT_WRITES_DESCRIPTION[reg_idx].is_empty() == false);
            false
        } else {
            debug_assert!(Self::INDIRECT_WRITES_DESCRIPTION[reg_idx].is_empty());
            true
        }
    }
}
