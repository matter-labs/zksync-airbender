use super::*;
use crate::witness::*;

pub mod add_sub_family;
pub mod binary_shifts_family;
pub mod jump_branch_slt_family;
pub mod memory;
pub mod mul_div;

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
pub(crate) fn touch_x0_with_ts<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(
    state: &mut State<C>,
) -> TimestampScalar {
    unsafe {
        let reg = state.registers.get_unchecked_mut(0 as usize);
        let ts = reg.timestamp;
        debug_assert!(ts < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        ts
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
pub(crate) fn write_register_with_ts_for_pure_opcode<
    C: Counters,
    const TIMESTAMP_OFFSET: TimestampScalar,
>(
    state: &mut State<C>,
    reg_idx: u8,
    value: u32,
) -> (u32, TimestampScalar) {
    debug_assert_ne!(reg_idx, 0);
    unsafe {
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        let existing_value = reg.value;
        let ts = reg.timestamp;
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        reg.value = value;

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
