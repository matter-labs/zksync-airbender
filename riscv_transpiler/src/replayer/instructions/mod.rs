use super::*;

use risc_v_simulator::machine_mode_only_unrolled::{
    LoadOpcodeTracingData, MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingData,
    NonMemoryOpcodeTracingDataWithTimestamp, StoreOpcodeTracingData,
};

pub mod add_sub;
pub mod binary;
pub mod branch;
pub mod jal_jalr;
pub mod lui_auipc;
pub mod memory;
pub mod mop;
pub mod mul_div;
pub mod shifts;
pub mod slt;
pub mod zicsr;

#[inline(always)]
pub(crate) fn read_register_with_ts<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(
    state: &mut State<C>,
    reg_idx: u8,
) -> (u32, TimestampScalar) {
    unsafe {
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        let existing_value = reg.value;
        let ts = reg.timestamp;
        debug_assert!(ts < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        (existing_value, ts)
    }
}

#[inline(always)]
pub(crate) fn write_register_with_ts<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(
    state: &mut State<C>,
    reg_idx: u8,
    value: &mut u32,
) -> (u32, TimestampScalar) {
    unsafe {
        if reg_idx == 0 {
            *value = 0;
        }
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        let existing_value = reg.value;
        let ts = reg.timestamp;
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        reg.value = *value;

        (existing_value, ts)
    }
}

#[inline(always)]
pub(crate) fn default_increase_pc<C: Counters>(state: &mut State<C>) {
    state.pc = state.pc.wrapping_add(core::mem::size_of::<u32>() as u32);
}

#[inline(always)]
pub(crate) fn illegal<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    panic!("Illegal instruction encounteted at PC = 0x{:08x}", state.pc);
}
