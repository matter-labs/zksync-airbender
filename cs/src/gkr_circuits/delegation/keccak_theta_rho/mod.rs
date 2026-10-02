// Theta/rho (precompile code 3), iteration x: lane pi_r[x + 5y] <- rotl(lane ^ D[x], rho[x][y]),
// D[x] = C[x - 1] ^ rotl(C[x + 1], 1) read from parity slots that are written back unchanged (the
// delegation ABI has no mixed read/write indirects per register). Each byte is xored and split at
// s = rho mod 8 by one lookup; the control table pins the one-hot flags that select rho.

use super::keccak_f1600_gadgets::{
    control_key, control_register, split_bytes, split_nibbles, state_lanes, tie_unchanged,
};
use super::*;
use crate::cs::circuit::*;
use crate::definitions::*;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use common_constants::delegation_types::keccak_f1600::{
    KECCAK_F1600_RHO, KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
};
use common_constants::delegation_types::keccak_special5::{ITERATION_BITS, PRECOMPILE_MODE_BITS};
use core::array::from_fn;

pub use common_constants::delegation_types::keccak_f1600::KECCAK_THETA_RHO_CSR_REGISTER;

const TOTAL_TABLE_WIDTH: usize = 8;

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry,
        TableType::KeccakThetaRhoDIndices,
        TableType::KeccakThetaRhoControl,
        TableType::KeccakXorSplit,
        TableType::KeccakRot1XorNibble,
    ]
}

pub fn keccak_theta_rho_delegation_circuit_table_addition_fn<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    for el in all_table_types() {
        cs.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn keccak_theta_rho_delegation_circuit_table_driver_fn<F: PrimeField>(
    table_driver: &mut TableDriver<F>,
) {
    for el in all_table_types() {
        table_driver.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn define_keccak_theta_rho_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _invocation_ts) =
        cs.allocate_delegation_state(KECCAK_THETA_RHO_CSR_REGISTER as u16);
    let (control, control_next) = control_register(cs);
    let control_key = control_key(control, execute);

    // 5 lanes, then C[x - 1] and C[x + 1] written back unchanged
    let indices: [Variable; KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS] = from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = state_lanes(cs, indices);
    tie_unchanged(cs, lanes_in[5], lanes_out[5]);
    tie_unchanged(cs, lanes_in[6], lanes_out[6]);
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, { KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS + 1 }, _>(|i| match i {
            0 => LookupInput::from(control_key.clone()),
            _ => LookupInput::from(indices[i - 1]),
        }),
        TableType::KeccakThetaRhoDIndices,
        false,
    );
    let c_prev = split_nibbles(cs, lanes_in[5]);
    let c_next = split_nibbles(cs, lanes_in[6]);
    let d_nibbles: [Variable; 16] = from_fn(|k| {
        let nibble = cs.add_variable();
        cs.set_variables_from_lookup_constrained(
            &[
                c_next[(k + 15) % 16].clone(),
                c_next[k].clone(),
                c_prev[k].clone(),
            ]
            .map(LookupInput::from),
            &[nibble],
            LookupQueryTableType::Constant(TableType::KeccakRot1XorNibble),
        );
        nibble
    });
    let d: [Expr<F>; 8] = from_fn(|j| {
        Expr::var(d_nibbles[2 * j]) + Expr::from(16u32) * Expr::var(d_nibbles[2 * j + 1])
    });

    let flags: [Variable; 5] = from_fn(|_| cs.add_variable());
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let iteration = placer
            .get_u16(control)
            .shr(PRECOMPILE_MODE_BITS as u32)
            .and(&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                (1 << ITERATION_BITS) - 1,
            ));
        let execute = placer.get_boolean(execute);
        for x in 0..5 {
            let flag = iteration.equal_to_constant(x as u16).and(&execute);
            placer.assign_mask(flags[x], &flag);
        }
    });
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, 7, _>(|i| match i {
            0 => LookupInput::from(control_key.clone()),
            1 => LookupInput::from(control_next),
            _ => LookupInput::from(flags[i - 2]),
        }),
        TableType::KeccakThetaRhoControl,
        false,
    );

    for y in 0..5 {
        let a = split_bytes(cs, lanes_in[y]);
        let shift = Expr::sum(
            (0..5)
                .map(|x| Expr::from(KECCAK_F1600_RHO[x][y] % 8) * Expr::var(flags[x]))
                .collect(),
        );
        let fragments: [[Variable; 2]; 8] = from_fn(|j| {
            let fragment = from_fn(|_| cs.add_variable());
            cs.set_variables_from_lookup_constrained(
                &[a[j].clone(), d[j].clone(), shift.clone()].map(LookupInput::from),
                &fragment,
                LookupQueryTableType::Constant(TableType::KeccakXorSplit),
            );
            fragment
        });
        for m in 0..4 {
            let mut terms = vec![];
            for x in 0..5 {
                let rotation = KECCAK_F1600_RHO[x][y] as usize;
                let (q, s) = (rotation / 8, rotation % 8);
                for (k, weight) in [(2 * m, 1u32), (2 * m + 1, 256)] {
                    terms.push(
                        Expr::from(weight)
                            * Expr::var(flags[x])
                            * Expr::var(fragments[(k + 8 - q) % 8][0]),
                    );
                    if s != 0 {
                        terms.push(
                            Expr::from(weight)
                                * Expr::var(flags[x])
                                * Expr::var(fragments[(k + 7 - q) % 8][1]),
                        );
                    }
                }
            }
            cs.add_constraint_expr(Expr::sum(terms) - Expr::var(lanes_out[y][m]));
        }
    }
}

#[cfg(test)]
pub(crate) mod test;
