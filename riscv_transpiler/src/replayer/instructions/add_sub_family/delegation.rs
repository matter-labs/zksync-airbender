use super::*;

#[inline(always)]
pub(crate) fn call_delegation<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.rd, 0);

    let delegation_type = match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16
        }
        a if a == DelegationType::Blake as u32 => {
            common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16
        }
        a if a == DelegationType::Keccak as u32 => {
            common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    };

    // and then trigger delegation
    match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            delegations::bigint::bigint_call::<C, R>(state, ram, tracer)
        }
        a if a == DelegationType::Blake as u32 => {
            delegations::blake2_round_function::blake2_round_function_call::<C, R>(
                state, ram, tracer,
            )
        }
        a if a == DelegationType::Keccak as u32 => {
            delegations::keccak_special5::keccak_special5_call::<C, R>(state, ram, tracer);
        }
        a if a == DelegationType::BlakeGFunction as u32 => {
            delegations::blake2_g_function::blake2_g_function_call::<C, R>(state, ram, tracer);
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}
