use std::fmt::Debug;

use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::*;
use crate::cycle::state::RiscV32State;
use crate::cycle::status_registers::TrapReason;
use crate::mmu::MMUImplementation;

pub trait CustomCSRProcessor: 'static + Clone + Debug {
    // we are only interested in CSRs that are NOT in out basic list
    fn process_read<
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
        zimm: u32,
        ret_val: &mut u32,
        trap: &mut TrapReason,
    );
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
        zimm: u32,
        trap: &mut TrapReason,
    );
}

#[derive(Clone, Copy, Debug)]
pub struct NoExtraCSRs;

impl CustomCSRProcessor for NoExtraCSRs {
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
        _csr_index: u32,
        _rs1_value: u32,
        _zimm: u32,
        ret_val: &mut u32,
        trap: &mut TrapReason,
    ) {
        *ret_val = 0;
        *trap = TrapReason::IllegalInstruction;
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
        _state: &mut RiscV32State<C>,
        _memory_source: &mut M,
        _non_determinism_source: &mut ND,
        _tracer: &mut TR,
        _mmu: &mut MMU,
        _csr_index: u32,
        _rs1_value: u32,
        _zimm: u32,
        trap: &mut TrapReason,
    ) {
        *trap = TrapReason::IllegalInstruction;
    }
}
