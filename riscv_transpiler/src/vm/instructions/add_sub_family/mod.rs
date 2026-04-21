use super::*;

pub(crate) mod add_sub;
pub(crate) mod auipc;
pub(crate) mod delegation;
pub(crate) mod mop;
pub(crate) mod non_determinism;

#[inline(always)]
pub(crate) fn nop_op<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.imm, 0);
    debug_assert_eq!(instr.rd, 0);

    touch_x0::<C, 0>(state);
    touch_x0::<C, 1>(state);
    touch_x0::<C, 2>(state);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
