use crate::cycle::{state::RiscV32State, state_new::RiscV32StateForUnrolledProver, MachineConfig};
use cs::definitions::{TimestampData, TimestampScalar};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BatchAccessPartialData {
    Read { read_value: u32 },
    Write { read_value: u32, written_value: u32 },
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadData {
    pub read_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadWriteData {
    pub read_value: u32,
    pub write_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadWriteData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        write_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

pub trait Tracer<C: MachineConfig>: Sized {
    #[inline(always)]
    fn at_cycle_start(&mut self, _current_state: &RiscV32State<C>) {}

    #[inline(always)]
    fn at_cycle_end(&mut self, _current_state: &RiscV32State<C>) {}

    #[inline(always)]
    fn at_cycle_start_ext(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {}

    #[inline(always)]
    fn at_cycle_end_ext(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {}

    #[inline(always)]
    fn trace_opcode_read(&mut self, _phys_address: u64, _read_value: u32) {}

    #[inline(always)]
    fn trace_rs1_read(&mut self, _reg_idx: u32, _read_value: u32) {}

    #[inline(always)]
    fn trace_rs2_read(&mut self, _reg_idx: u32, _read_value: u32) {}

    #[inline(always)]
    fn trace_rd_write(&mut self, _reg_idx: u32, _read_value: u32, _written_value: u32) {}

    #[inline(always)]
    fn trace_non_determinism_read(&mut self, _read_value: u32) {}

    #[inline(always)]
    fn trace_non_determinism_write(&mut self, _written_value: u32) {}

    #[inline(always)]
    fn trace_ram_read(&mut self, _phys_address: u64, _read_value: u32) {}

    #[inline(always)]
    fn trace_ram_read_write(&mut self, _phys_address: u64, _read_value: u32, _written_value: u32) {}

    #[inline(always)]
    fn trace_address_translation(
        &mut self,
        _satp_value: u32,
        _virtual_address: u64,
        _phys_address: u64,
    ) {
    }

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

impl<C: MachineConfig> Tracer<C> for () {}
