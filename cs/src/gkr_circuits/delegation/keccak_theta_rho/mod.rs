// Keccak-f1600 as 361 delegation calls. The state is 25 u64 lanes A[x, y], indices mod 5, and
// each of the 24 rounds r is
//
//   theta  C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]
//          D[x] = C[x - 1] ^ rotl(C[x + 1], 1)  <- this circuit
//          A[x, y] ^= D[x]  <- this circuit
//   rho    A[x, y] = rotl(A[x, y], rho[x][y])  <- this circuit
//   pi     B[y, 2x + 3y] = A[x, y]
//   chi    A[x, y] = B[x, y] ^ (!B[x + 1, y] & B[x + 2, y])
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
// This circuit, precompile code 3, call x of round r: reads C[x - 1] and C[x + 1] from slots
// 25 + (x - 1) and 25 + (x + 1), read only, and computes D[x] one byte at a time with a xor
// lookup, rotl(C[x + 1], 1) being affine in the u16 limbs of C[x + 1] and their top bits. It then
// replaces each lane of column x, at slot P_r[x + 5y], by rotl(A[x, y] ^ D[x], rho[x][y]): one
// lookup xors each byte with D and splits it at rho mod 8, and byte placement does the rest of the
// rotation. The control table pins the one-hot flags that
// select the column's rho offsets.
//
// Read timestamps: x10 and x11 share one committed read timestamp, as the previous call always
// touches both; the ten state-lane words share one, as column parity x touched all five lanes
// at once; the two words of each parity share one. The distances from the invocation are fixed
// by the canonical call sequence, see docs/keccak_relative_read_timestamps.md.

use super::keccak_f1600_gadgets::{
    control_key, grouped_control_register, grouped_state_lanes, read_timestamp_distance,
    set_registers_read_timestamp_distance, split_bytes, REGISTERS_READ_TIMESTAMP_GROUP,
};
use super::*;
use crate::cs::circuit::*;
use crate::definitions::*;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use common_constants::delegation_types::keccak_f1600::{
    KECCAK_F1600_RHO, KECCAK_THETA_RHO_LANE_READ_DISTANCE, KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
    KECCAK_THETA_RHO_PARITY_READ_DISTANCES,
};
use common_constants::delegation_types::keccak_special5::{ITERATION_BITS, PRECOMPILE_MODE_BITS};
use core::array::from_fn;

pub use common_constants::delegation_types::keccak_f1600::KECCAK_THETA_RHO_CSR_REGISTER;

const TOTAL_TABLE_WIDTH: usize = 8;

const LANES_READ_TIMESTAMP_GROUP: u8 = 1;
const PARITY_READ_TIMESTAMP_GROUPS: [u8; 2] = [2, 3];

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::KeccakThetaRhoDIndices,
        TableType::KeccakThetaRhoControl,
        TableType::KeccakXorSplit,
        TableType::Xor,
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
    let (control, control_next) =
        grouped_control_register(cs, Some(REGISTERS_READ_TIMESTAMP_GROUP));
    let control_key = control_key(control, execute);

    // 5 lanes, then C[x - 1] and C[x + 1], read only
    let indices: [Variable; KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS] = from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = grouped_state_lanes(
        cs,
        indices,
        from_fn(|i| i < 5),
        Some(REGISTERS_READ_TIMESTAMP_GROUP),
        from_fn(|i| {
            Some(if i < 5 {
                LANES_READ_TIMESTAMP_GROUP
            } else {
                PARITY_READ_TIMESTAMP_GROUPS[i - 5]
            })
        }),
    );
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, { KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS + 1 }, _>(|i| match i {
            0 => LookupInput::from(control_key.clone()),
            _ => LookupInput::from(indices[i - 1]),
        }),
        TableType::KeccakThetaRhoDIndices,
        false,
    );
    let c_prev = split_bytes(cs, lanes_in[5]);
    let c_next = lanes_in[6];
    let top: [Variable; 4] = from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
    let rotated_low: [Variable; 4] = from_fn(|_| cs.add_variable());
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let mask = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0xff);
        for m in 0..4 {
            let limb = placer.get_u16(c_next[m]);
            let carry = placer.get_u16(c_next[(m + 3) % 4]).shr(15);
            placer.assign_mask(top[m], &limb.get_bit(15));
            placer.assign_u16(rotated_low[m], &limb.shl(1).or(&carry).and(&mask));
        }
    });
    let inv256 = F::from_u32_unchecked(256).inverse().unwrap();
    let rotated: [[Expr<F>; 2]; 4] = from_fn(|m| {
        let limb = Expr::from(2u32) * Expr::var(c_next[m]) + Expr::var(top[(m + 3) % 4])
            - Expr::from(1u32 << 16) * Expr::var(top[m]);
        [
            Expr::var(rotated_low[m]),
            (limb - Expr::var(rotated_low[m])) * Expr::constant(inv256),
        ]
    });
    let d: [Expr<F>; 8] = from_fn(|j| {
        let byte = cs.add_variable();
        cs.set_variables_from_lookup_constrained(
            &[c_prev[j / 2][j % 2].clone(), rotated[j / 2][j % 2].clone()].map(LookupInput::from),
            &[byte],
            LookupQueryTableType::Constant(TableType::Xor),
        );
        Expr::var(byte)
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
        &from_fn::<_, 8, _>(|i| match i {
            0 => LookupInput::from(control),
            1 => LookupInput::from(execute),
            2 => LookupInput::from(control_next),
            _ => LookupInput::from(flags[i - 3]),
        }),
        TableType::KeccakThetaRhoControl,
        false,
    );
    set_registers_read_timestamp_distance(cs, execute);
    cs.set_read_timestamp_group_distance(
        LANES_READ_TIMESTAMP_GROUP,
        read_timestamp_distance(
            Expr::from(KECCAK_THETA_RHO_LANE_READ_DISTANCE as u32) * Expr::var(execute),
        ),
    );
    for (group, distances) in PARITY_READ_TIMESTAMP_GROUPS
        .into_iter()
        .zip(KECCAK_THETA_RHO_PARITY_READ_DISTANCES)
    {
        cs.set_read_timestamp_group_distance(
            group,
            read_timestamp_distance(Expr::sum(
                (0..5)
                    .map(|x| Expr::from(distances[x] as u32) * Expr::var(flags[x]))
                    .collect(),
            )),
        );
    }

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
                &[a[j / 2][j % 2].clone(), d[j].clone(), shift.clone()].map(LookupInput::from),
                &fragment,
                LookupQueryTableType::Constant(TableType::KeccakXorSplit),
            );
            fragment
        });
        // byte k of rotl(v, 8q + s) is fragment 0 of byte k - q plus, unless s = 0, fragment 1 of
        // byte k - q - 1
        let rotated_byte = |k: usize, rotation: u32| {
            let (q, s) = ((rotation / 8) as usize, rotation % 8);
            let low = fragments[(k + 8 - q) % 8][0];
            let high = (s != 0).then(|| fragments[(k + 7 - q) % 8][1]);
            [Some(low), high].into_iter().flatten()
        };
        for m in 0..4 {
            let mut terms = vec![];
            for x in 0..5 {
                for (k, weight) in [(2 * m, 1u32), (2 * m + 1, 256)] {
                    for fragment in rotated_byte(k, KECCAK_F1600_RHO[x][y]) {
                        terms.push(Expr::from(weight) * Expr::var(flags[x]) * Expr::var(fragment));
                    }
                }
            }
            cs.add_constraint_expr(Expr::sum(terms) - Expr::var(lanes_out[y][m]));
        }
    }
}

#[cfg(test)]
pub(crate) mod test;
