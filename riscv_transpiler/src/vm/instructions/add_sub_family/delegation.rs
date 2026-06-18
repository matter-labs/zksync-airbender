use super::*;

#[inline(always)]
pub(crate) fn call_delegation<C: Counters, S: Snapshotter<C>, R: RAM, E: ExecutionObserver<C>>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.rd, 0);

    // NOTE: for simulator purposes we do not need to track "formal" reads from the corresponding CSR

    // and then trigger delegation - internals are responsible to move machine state in full,
    // especially in case of multiple delegation calls batched together
    match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            delegations::bigint::bigint_call::<C, S, R, E>(state, ram, snapshotter)
        }
        a if a == DelegationType::Blake as u32 => {
            delegations::blake2_round_function::blake2_round_function_call::<C, S, R, E>(
                state,
                ram,
                snapshotter,
            )
        }
        a if a == DelegationType::Keccak as u32 => {
            delegations::keccak_special5::keccak_special5_call::<C, S, R, E>(
                state,
                ram,
                snapshotter,
            )
        }
        a if a == DelegationType::BlakeGFunction as u32 => {
            delegations::blake2_g_function::blake2_g_function_call::<C, S, R, E>(
                state,
                ram,
                snapshotter,
            )
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}
