use crate::abstractions::csr_processor::CustomCSRProcessor;
use crate::abstractions::memory::*;
use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::tracer::*;
use crate::cycle::state::RiscV32State;
use crate::cycle::status_registers::TrapReason;
use crate::cycle::MachineConfig;
use crate::mmu::*;
use cs::definitions::TimestampScalar;
use std::mem::MaybeUninit;
use std::ops::Range;

pub mod blake2_round_function_with_compression_mode;
pub mod u256_ops_with_control;

#[derive(Clone, Copy, Debug)]
pub struct DelegationsCSRProcessor;

pub(crate) fn register_indirect_read_continuous_noexcept<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    memory_source: &mut M,
) -> [RegisterOrIndirectReadData; N] {
    let mut result = [RegisterOrIndirectReadData::EMPTY; N];

    unsafe {
        let mut address = base_mem_offset;
        for i in 0..N {
            let read_value = memory_source.get_noexcept(address as u64);
            result.get_unchecked_mut(i).read_value = read_value;

            address += core::mem::size_of::<u32>();
        }
    }

    result
}

pub(crate) fn register_indirect_read_write_continuous_noexcept<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    memory_source: &mut M,
) -> [RegisterOrIndirectReadWriteData; N] {
    let mut result = [RegisterOrIndirectReadWriteData::EMPTY; N];

    unsafe {
        let mut address = base_mem_offset;
        for i in 0..N {
            let read_value = memory_source.get_noexcept(address as u64);
            result.get_unchecked_mut(i).read_value = read_value;

            address += core::mem::size_of::<u32>();
        }
    }

    result
}

#[track_caller]
pub(crate) fn write_indirect_accesses_noexcept<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    accesses: &[RegisterOrIndirectReadWriteData; N],
    memory_source: &mut M,
) {
    let mut address = base_mem_offset;
    for src in accesses {
        memory_source.set_noexcept(address as u64, src.write_value);

        address += core::mem::size_of::<u32>();
    }
}
