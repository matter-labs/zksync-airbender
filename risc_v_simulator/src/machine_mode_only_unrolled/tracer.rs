use super::*;
use crate::abstractions::tracer::{RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData};

// NOTE: We assume that tracer can timestamp by itself

pub trait UnrolledTracer<C: MachineConfig>: Sized {
    #[inline(always)]
    fn at_cycle_start(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {}

    #[inline(always)]
    fn at_cycle_end(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {}

    #[inline(always)]
    fn trace_decoder_step(&mut self, data: TracingDecoderData) {}

    #[inline(always)]
    fn trace_non_mem_step(&mut self, family: u8, data: NonMemoryOpcodeTracingData) {}

    #[inline(always)]
    fn trace_mem_load_step(&mut self, data: LoadOpcodeTracingData) {}

    #[inline(always)]
    fn trace_mem_store_step(&mut self, data: StoreOpcodeTracingData) {}

    #[inline(always)]
    fn record_delegation(
        &mut self,
        _access_id: u32,
        _base_register: u32,
        _register_accesses: &mut [RegisterOrIndirectReadWriteData],
        _indirect_read_addresses: &[u32],
        _indirect_reads: &mut [RegisterOrIndirectReadData],
        _indirect_write_addresses: &[u32],
        _indirect_writes: &mut [RegisterOrIndirectReadWriteData],
    ) {
    }
}

impl<C: MachineConfig> UnrolledTracer<C> for () {}
