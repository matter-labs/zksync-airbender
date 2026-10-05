// Keccak-f1600 as 361 delegation calls. The state is 25 u64 lanes A[x, y], indices mod 5, and
// each of the 24 rounds r is
//
//   theta  C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]  <- this circuit
//          D[x] = C[x - 1] ^ rotl(C[x + 1], 1)
//          A[x, y] ^= D[x]
//   rho    A[x, y] = rotl(A[x, y], rho[x][y])
//   pi     B[y, 2x + 3y] = A[x, y]
//   chi    A[x, y] = B[x, y] ^ (!B[x + 1, y] & B[x + 2, y])
//   iota   A[0, 0] ^= RC[r]  <- this circuit
//
// A round makes five column parity calls (C[x], x = 0..4), five theta/rho calls (D[x], then theta
// and rho on column x) and five chi5 calls (row y = 0..4). Iota is delayed: column parity call
// x = 0 of round r first applies RC[r - 1] (nothing in round 0), and a final column parity call
// in round 24 applies RC[23]. The lanes live in keccak_special5's 31-slot state at x11: during
// round r lane A[x, y] is at slot P_r[x + 5y], P_r = KECCAK_F1600_PERMUTATIONS[r], so pi moves no
// data and only switches the slot map to P_(r+1). Slot 25 + x holds C[x] and slot 30 is unused.
// x10 holds the control word precompile | call << 3 | r << 6.
//
// This circuit, precompile code 0, call x of round r: reads the lanes of column x at slots
// P_r[x + 5y], y = 0..4; for x = 0 it first xors RC[r - 1] into A[0, 0] (round 24 is only this
// final iota), then writes C[x] to slot 25 + x. The other four lanes are read only. A five-input
// xor lookup computes C[x] one nibble at a time; iota lookups tie the first lane's written value to
// its read value on the only bytes where round constants have bits.

use super::keccak_f1600_gadgets::{
    control_key, control_register, split_bytes, split_nibbles, state_lanes,
};
use super::*;
use crate::definitions::*;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use common_constants::delegation_types::keccak_f1600::KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS;
use common_constants::delegation_types::keccak_special5::{ITERATION_BITS, PRECOMPILE_MODE_BITS};
use core::array::from_fn;

pub use common_constants::delegation_types::keccak_f1600::KECCAK_COLUMN_PARITY_CSR_REGISTER;

const IOTA_BYTES: [usize; 4] = [0, 1, 3, 7];

const TOTAL_TABLE_WIDTH: usize = 7;

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry,
        TableType::KeccakColumnParityIndices,
        TableType::KeccakColumnParityControl,
        TableType::KeccakXor5Nibble,
        TableType::XorSpecialIota,
    ]
}

pub fn keccak_column_parity_delegation_circuit_table_addition_fn<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    for el in all_table_types() {
        cs.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn keccak_column_parity_delegation_circuit_table_driver_fn<F: PrimeField>(
    table_driver: &mut TableDriver<F>,
) {
    for el in all_table_types() {
        table_driver.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn define_keccak_column_parity_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _invocation_ts) =
        cs.allocate_delegation_state(KECCAK_COLUMN_PARITY_CSR_REGISTER as u16);
    let (control, control_next) = control_register(cs);
    let control_key = control_key(control, execute);

    let indices: [Variable; KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS] =
        from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = state_lanes(cs, indices, [true, false, false, false, false, true]);
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, { KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS + 1 }, _>(|i| match i {
            0 => LookupInput::from(control_key.clone()),
            _ => LookupInput::from(indices[i - 1]),
        }),
        TableType::KeccakColumnParityIndices,
        false,
    );

    let iota_round = cs.add_variable();
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let control = placer.get_u16(control);
        let first = control
            .and(&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                (1 << (PRECOMPILE_MODE_BITS + ITERATION_BITS)) - 1,
            ))
            .equal_to_constant(0)
            .and(&placer.get_boolean(execute));
        let round = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
            &first,
            &control.shr((PRECOMPILE_MODE_BITS + ITERATION_BITS) as u32),
            &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0),
        );
        placer.assign_u16(iota_round, &round);
    });
    cs.enforce_lookup_tuple_for_fixed_table(
        &[
            LookupInput::from(control),
            LookupInput::from(execute),
            LookupInput::from(control_next),
            LookupInput::from(iota_round),
        ],
        TableType::KeccakColumnParityControl,
        false,
    );

    let first_lane_in = split_bytes(cs, lanes_in[0]);
    let first_lane = split_nibbles(cs, lanes_out[0]);
    for j in 0..8 {
        let written = first_lane[2 * j].clone() + Expr::from(16u32) * first_lane[2 * j + 1].clone();
        if IOTA_BYTES.contains(&j) {
            cs.enforce_lookup_tuple_for_fixed_table(
                &[
                    LookupInput::from(first_lane_in[j].clone()),
                    LookupInput::from(Expr::var(iota_round) + Expr::from(32 * j as u32)),
                    LookupInput::from(written),
                ],
                TableType::XorSpecialIota,
                false,
            );
        } else {
            cs.add_constraint_expr_allow_explicit_linear(first_lane_in[j].clone() - written);
        }
    }

    let others: [[Expr<F>; 16]; 4] = from_fn(|y| split_nibbles(cs, lanes_in[y + 1]));
    let parity = split_nibbles(cs, lanes_out[5]);
    for k in 0..16 {
        cs.enforce_lookup_tuple_for_fixed_table(
            &from_fn::<_, 6, _>(|i| match i {
                0 => LookupInput::from(first_lane[k].clone()),
                1..5 => LookupInput::from(others[i - 1][k].clone()),
                _ => LookupInput::from(parity[k].clone()),
            }),
            TableType::KeccakXor5Nibble,
            false,
        );
    }
}

#[cfg(test)]
mod test;
