use u256_ops_with_control::u256_ops_with_control_impl;
use u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID;

use blake2_round_function_with_compression_mode::blake2_round_function_with_extended_control;
use blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID;

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

pub mod unrolled;

pub mod blake2_round_function_with_compression_mode;
pub mod u256_ops_with_control;

#[derive(Clone, Copy, Debug)]
pub struct DelegationsCSRProcessor;

pub(crate) fn read_words_at_offsets_into<'a, M: MemorySource>(
    base_mem_offset: usize,
    words_range: Range<usize>,
    is_write_access: bool,
    memory_source: &mut M,
    trap: &mut TrapReason,
    destination: &mut impl ExactSizeIterator<Item = &'a mut u32>,
    accesses_bookkeeping_iterator: &mut impl ExactSizeIterator<Item = &'a mut BatchAccessPartialData>,
) {
    assert_eq!(words_range.len(), destination.len());
    assert!(words_range.len() <= accesses_bookkeeping_iterator.len());

    for ((offset, dst), bookkeeping_dst) in words_range
        .zip(destination)
        .zip(accesses_bookkeeping_iterator)
    {
        let address: usize = base_mem_offset + offset * core::mem::size_of::<u32>();
        let read_value = memory_source.get(address as u64, AccessType::RegWrite, trap);
        if trap.is_a_trap() {
            panic!("error in memory access");
        }

        let record = if is_write_access {
            BatchAccessPartialData::Write {
                read_value: read_value,
                written_value: 0,
            }
        } else {
            BatchAccessPartialData::Read {
                read_value: read_value,
            }
        };

        *dst = read_value;
        *bookkeeping_dst = record;
    }
}

#[track_caller]
pub(crate) fn write_words_at_offsets_into<'a, M: MemorySource>(
    base_mem_offset: usize,
    words_range: Range<usize>,
    memory_source: &mut M,
    trap: &mut TrapReason,
    source: &mut impl ExactSizeIterator<Item = &'a u32>,
    accesses_bookkeeping_iterator: &mut impl ExactSizeIterator<Item = &'a mut BatchAccessPartialData>,
) {
    assert_eq!(words_range.len(), source.len());
    assert!(words_range.len() <= accesses_bookkeeping_iterator.len());

    // after we checked length equality, we can move the address calculation out of cycle
    let mut address = base_mem_offset + words_range.start * core::mem::size_of::<u32>();
    for (src, bookkeeping_dst) in source.zip(accesses_bookkeeping_iterator) {
        memory_source.set(address as u64, *src, AccessType::RegWrite, trap);
        if trap.is_a_trap() {
            panic!("error in memory access");
        }

        let BatchAccessPartialData::Write { written_value, .. } = bookkeeping_dst else {
            panic!("trying to write into readonly access record");
        };

        *written_value = *src;
        address += core::mem::size_of::<u32>();
    }
}

pub(crate) fn read_continuous_words<'a, M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    is_write_access: bool,
    memory_source: &mut M,
    trap: &mut TrapReason,
    bookkeeping: &mut [BatchAccessPartialData; N],
) -> [u32; N] {
    let mut result = [0u32; N];

    unsafe {
        let mut address = base_mem_offset;
        for i in 0..N {
            let read_value = memory_source.get(address as u64, AccessType::RegWrite, trap);
            if trap.is_a_trap() {
                panic!("error in memory access");
            }

            *result.get_unchecked_mut(i) = read_value;
            let record = if is_write_access {
                BatchAccessPartialData::Write {
                    read_value: read_value,
                    written_value: 0,
                }
            } else {
                BatchAccessPartialData::Read {
                    read_value: read_value,
                }
            };
            *bookkeeping.get_unchecked_mut(i) = record;

            address += core::mem::size_of::<u32>();
        }
    }

    result
}

pub(crate) fn register_indirect_read_continuous<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    memory_source: &mut M,
) -> [RegisterOrIndirectReadData; N] {
    let mut result = [RegisterOrIndirectReadData::EMPTY; N];

    let mut trap = TrapReason::NoTrap;
    unsafe {
        let mut address = base_mem_offset;
        for i in 0..N {
            let read_value = memory_source.get(address as u64, AccessType::RegWrite, &mut trap);
            if trap.is_a_trap() {
                panic!("error in memory access");
            }
            result.get_unchecked_mut(i).read_value = read_value;

            address += core::mem::size_of::<u32>();
        }
    }

    result
}

pub(crate) fn register_indirect_read_write_continuous<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    memory_source: &mut M,
) -> [RegisterOrIndirectReadWriteData; N] {
    let mut result = [RegisterOrIndirectReadWriteData::EMPTY; N];

    let mut trap = TrapReason::NoTrap;
    unsafe {
        let mut address = base_mem_offset;
        for i in 0..N {
            let read_value = memory_source.get(address as u64, AccessType::RegWrite, &mut trap);
            if trap.is_a_trap() {
                panic!("error in memory access");
            }
            result.get_unchecked_mut(i).read_value = read_value;

            address += core::mem::size_of::<u32>();
        }
    }

    result
}

#[track_caller]
pub(crate) fn write_indirect_accesses<M: MemorySource, const N: usize>(
    base_mem_offset: usize,
    accesses: &[RegisterOrIndirectReadWriteData; N],
    memory_source: &mut M,
) {
    let mut trap = TrapReason::NoTrap;

    let mut address = base_mem_offset;
    for src in accesses {
        memory_source.set(
            address as u64,
            src.write_value,
            AccessType::RegWrite,
            &mut trap,
        );
        if trap.is_a_trap() {
            panic!("error in memory access");
        }

        address += core::mem::size_of::<u32>();
    }
}

pub(crate) fn read_single_value<'a, M: MemorySource>(
    base_mem_offset: usize,
    word_index: usize,
    is_write_access: bool,
    memory_source: &mut M,
    trap: &mut TrapReason,
    bookkeeping_record: &mut BatchAccessPartialData,
) -> u32 {
    let address: usize = base_mem_offset + word_index * core::mem::size_of::<u32>();
    let read_value = memory_source.get(address as u64, AccessType::RegWrite, trap);
    if trap.is_a_trap() {
        panic!("error in memory access");
    }

    let record = if is_write_access {
        BatchAccessPartialData::Write {
            read_value: read_value,
            written_value: 0,
        }
    } else {
        BatchAccessPartialData::Read {
            read_value: read_value,
        }
    };
    *bookkeeping_record = record;

    read_value
}

impl CustomCSRProcessor for DelegationsCSRProcessor {
    #[inline(always)]
    fn process_read<
        M: MemorySource,
        TR: Tracer<C>,
        ND: NonDeterminismCSRSource<M>,
        MMU: MMUImplementation<M, TR, C>,
        C: MachineConfig,
    >(
        &mut self,
        _state: &mut RiscV32State<C>,
        _memory_source: &mut M,
        _non_determinism_source: &mut ND,
        _tracer: &mut TR,
        _mmu: &mut MMU,
        csr_index: u32,
        _rs1_value: u32,
        _zimm: u32,
        ret_val: &mut u32,
        trap: &mut TrapReason,
    ) {
        *ret_val = 0;
        match csr_index {
            BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID => {}
            U256_OPS_WITH_CONTROL_ACCESS_ID => {}
            _ => {
                *trap = TrapReason::IllegalInstruction;
            }
        }
    }

    #[inline(always)]
    fn process_write<
        M: MemorySource,
        TR: Tracer<C>,
        ND: NonDeterminismCSRSource<M>,
        MMU: MMUImplementation<M, TR, C>,
        C: MachineConfig,
    >(
        &mut self,
        state: &mut RiscV32State<C>,
        memory_source: &mut M,
        non_determinism_source: &mut ND,
        tracer: &mut TR,
        mmu: &mut MMU,
        csr_index: u32,
        rs1_value: u32,
        _zimm: u32,
        trap: &mut TrapReason,
    ) {
        match csr_index {
            BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID => {
                blake2_round_function_with_extended_control(
                    state,
                    memory_source,
                    tracer,
                    mmu,
                    rs1_value,
                    trap,
                );
            }
            U256_OPS_WITH_CONTROL_ACCESS_ID => {
                u256_ops_with_control_impl(state, memory_source, tracer, mmu, rs1_value, trap);
            }
            _ => {
                *trap = TrapReason::IllegalInstruction;
            }
        }
    }
}
