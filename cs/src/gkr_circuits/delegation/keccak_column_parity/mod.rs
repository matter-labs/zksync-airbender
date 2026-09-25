// Column parity (precompile code 0), iteration x: slot 25 + x <- C[x] = xor of lanes pi_r[x + 5y];
// iteration 0 first xors the previous round's delayed iota into lane pi_r[0] (round 24 is only that
// final iota). The other four lanes are written back unchanged; the first lane's written value is
// tied to its read value by iota lookups on the only bytes where round constants have bits.

use super::keccak_theta_rho::{
    control_register, split_bytes, split_nibbles, state_lanes, tie_unchanged,
};
use super::*;
use crate::definitions::*;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
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

pub fn define_keccak_column_parity_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _invocation_ts) =
        cs.allocate_delegation_state(KECCAK_COLUMN_PARITY_CSR_REGISTER as u16);
    let (control, control_next) = control_register(cs);
    let control_key = Expr::var(control) + Expr::from(1u32 << 11) * Expr::var(execute);

    let indices: [Variable; 6] = from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = state_lanes(cs, indices);
    for y in 1..5 {
        tie_unchanged(cs, lanes_in[y], lanes_out[y]);
    }
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, 7, _>(|i| match i {
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
                0b111_111,
            ))
            .equal_to_constant(0)
            .and(&placer.get_boolean(execute));
        let round = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
            &first,
            &control.shr(6),
            &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0),
        );
        placer.assign_u16(iota_round, &round);
    });
    cs.enforce_lookup_tuple_for_fixed_table(
        &[
            LookupInput::from(control_key),
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
