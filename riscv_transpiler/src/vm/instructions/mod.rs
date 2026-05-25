use super::*;

pub mod add_sub_family;
pub mod binary_shifts_family;
pub mod jump_branch_slt_family;
pub mod memory;
pub mod mul_div;

#[inline(always)]
pub(crate) fn touch_x0<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(state: &mut State<C>) {
    unsafe {
        let reg = state.registers.get_unchecked_mut(0 as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
    }
}

#[inline(always)]
pub(crate) fn read_register<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(
    state: &mut State<C>,
    reg_idx: u8,
) -> u32 {
    unsafe {
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        reg.value
    }
}

#[inline(always)]
pub(crate) fn write_register_for_pure_opcode<
    C: Counters,
    const TIMESTAMP_OFFSET: TimestampScalar,
>(
    state: &mut State<C>,
    reg_idx: u8,
    value: u32,
) {
    debug_assert_ne!(reg_idx, 0);
    unsafe {
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        reg.value = value;
    }
}

#[inline(always)]
pub(crate) fn write_register<C: Counters, const TIMESTAMP_OFFSET: TimestampScalar>(
    state: &mut State<C>,
    reg_idx: u8,
    value: &mut u32,
) {
    unsafe {
        if reg_idx == 0 {
            *value = 0;
        }
        let reg = state.registers.get_unchecked_mut(reg_idx as usize);
        debug_assert!(reg.timestamp < (state.timestamp | TIMESTAMP_OFFSET));
        reg.timestamp = state.timestamp | TIMESTAMP_OFFSET;
        reg.value = *value;
    }
}

#[inline(always)]
pub(crate) fn default_increase_pc<C: Counters>(state: &mut State<C>) {
    state.pc = state.pc.wrapping_add(core::mem::size_of::<u32>() as u32);
}

#[inline(always)]
pub(crate) fn increment_family_counter<C: Counters, const FAMILY: u8>(state: &mut State<C>) {
    state.counters.log_circuit_family::<FAMILY>();
}

#[inline(always)]
pub(crate) fn illegal<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    _instr: Instruction,
) {
    panic!("Illegal instruction encounteted at PC = 0x{:08x}", state.pc);
}

#[inline(always)]
pub(crate) fn marker<C: Counters, S: Snapshotter<C>, R: RAM, E: ExecutionObserver<C>>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let _rs1_value = read_register::<C, 0>(state, instr.rs1);
    touch_x0::<C, 1>(state);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, 0);

    // Emit the observation before the instruction advances the cycle-family
    // counters or the outer execution loop bumps the timestamp.
    E::on_marker(state);

    default_increase_pc::<C>(state);
    // NOTE: it's only for tests, so we do not touch any instruction counter
}
