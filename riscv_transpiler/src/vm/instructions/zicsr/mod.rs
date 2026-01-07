use super::*;

#[inline(always)]
pub(crate) fn nd_read<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);

    touch_x0::<C, 1>(state);
    let mut rd = nd.read();
    snapshotter.append_arbitrary_value(rd);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn nd_write<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    touch_x0::<C, 1>(state);
    nd.write_with_memory_access(&*ram, rs1_value);
    write_register::<C, 2>(state, instr.rd, &mut 0);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn call_delegation<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.rd, 0);

    // and then trigger delegation - internals are responsible to move machine state in full,
    // especially in case of multiple delegation calls batched together
    match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            delegations::bigint::bigint_call(state, ram, snapshotter)
        }
        a if a == DelegationType::Blake as u32 => {
            delegations::blake2_round_function::blake2_round_function_call(state, ram, snapshotter)
        }
        a if a == DelegationType::Keccak as u32 => {
            delegations::keccak_special5::keccak_special5_call(state, ram, snapshotter)
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}
