// Keccak-f1600 as 361 delegation calls. The state is 25 u64 lanes A[x, y], indices mod 5, and
// each of the 24 rounds r is
//
//   theta  C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]
//          D[x] = C[x - 1] ^ rotl(C[x + 1], 1)
//          A[x, y] ^= D[x]
//   rho    A[x, y] = rotl(A[x, y], rho[x][y])
//   pi     B[y, 2x + 3y] = A[x, y]
//   chi    A[x, y] = B[x, y] ^ (!B[x + 1, y] & B[x + 2, y])  <- this circuit
//   iota   A[0, 0] ^= RC[r]
//
// A round makes five column parity calls (C[x], x = 0..4), five theta/rho calls (D[x], then theta
// and rho on column x) and five chi5 calls (row y = 0..4). Iota is delayed: column parity call
// x = 0 of round r first applies RC[r - 1] (nothing in round 0), and a final column parity call
// in round 24 applies RC[23]. The lanes live in keccak_special5's 31-slot state at x11: during
// round r lane A[x, y] is at slot P_r[x + 5y], P_r = KECCAK_F1600_PERMUTATIONS[r], so pi moves no
// data and only switches the slot map to P_(r+1). Slot 25 + x holds C[x] and slot 30 is unused.
// x10 holds the control word precompile | call << 3 | r << 6.
//
// This circuit, precompile code 5, call y of round r: replaces row y after pi, B[x, y] for x = 0..4
// at slots P_(r+1)[x + 5y], by its chi. One five-nibble chi lookup per 4-bit slice covers the 64
// bits. The call index is the row y here, not the column x as in the other two circuits.

use super::keccak_f1600_gadgets::{control_register, split_nibbles, state_lanes};
use super::*;
use crate::definitions::*;
use common_constants::delegation_types::keccak_f1600::KECCAK_CHI5_NUM_VARIABLE_OFFSETS;
use core::array::from_fn;

pub use common_constants::delegation_types::keccak_f1600::KECCAK_CHI5_CSR_REGISTER;

const TOTAL_TABLE_WIDTH: usize = 10;

pub fn all_table_types() -> Vec<TableType> {
    vec![TableType::KeccakChi5, TableType::KeccakChi5Control]
}

pub fn keccak_chi5_delegation_circuit_table_addition_fn<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    for el in all_table_types() {
        cs.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn keccak_chi5_delegation_circuit_table_driver_fn<F: PrimeField>(
    table_driver: &mut TableDriver<F>,
) {
    for el in all_table_types() {
        table_driver.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn define_keccak_chi5_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _invocation_ts) = cs.allocate_delegation_state(KECCAK_CHI5_CSR_REGISTER as u16);
    let (control, control_next) = control_register(cs);
    let indices: [Variable; KECCAK_CHI5_NUM_VARIABLE_OFFSETS] = from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = state_lanes(cs, indices, [true; KECCAK_CHI5_NUM_VARIABLE_OFFSETS]);
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, { KECCAK_CHI5_NUM_VARIABLE_OFFSETS + 3 }, _>(|i| match i {
            0 => LookupInput::from(control),
            1 => LookupInput::from(execute),
            2 => LookupInput::from(control_next),
            _ => LookupInput::from(indices[i - 3]),
        }),
        TableType::KeccakChi5Control,
        false,
    );
    let input = lanes_in.map(|limbs| split_nibbles(cs, limbs));
    let output = lanes_out.map(|limbs| split_nibbles(cs, limbs));
    for k in 0..16 {
        cs.enforce_lookup_tuple_for_fixed_table(
            &from_fn::<_, 10, _>(|i| {
                LookupInput::from(if i < 5 {
                    input[i][k].clone()
                } else {
                    output[i - 5][k].clone()
                })
            }),
            TableType::KeccakChi5,
            false,
        );
    }
}

#[cfg(test)]
mod test;
