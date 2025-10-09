use super::*;

#[inline(always)]
pub(crate) fn nd_read<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource<R>>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    let _rs1_value = read_register::<C, 0>(state, instr.rs1);
    let _rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut rd = nd.read();
    snapshotter.append_non_determinism_read(rd);
    state.counters.bump_non_determinism();
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn nd_write<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource<R>>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let _rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
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
    // NOTE: we still need to touch registers
    let _rs1_value = read_register::<C, 0>(state, instr.rs1);
    let _rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    write_register::<C, 2>(state, instr.rd, &mut 0);
    // and then trigger delegation
    match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            delegations::bigint::bigint_call(state, ram, snapshotter)
        }
        a if a == DelegationType::Blake as u32 => {
            delegations::blake2_round_function::blake2_round_function_call(state, ram, snapshotter)
        }
        a if a == DelegationType::Keccak as u32 => {
            todo!()
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}
