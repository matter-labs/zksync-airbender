// Theta/rho (precompile code 3), iteration x: lane pi_r[x + 5y] <- rotl(lane ^ D[x], rho[x][y]),
// D[x] = C[x - 1] ^ rotl(C[x + 1], 1) read from parity slots that are written back unchanged (the
// delegation ABI has no mixed read/write indirects per register). Each byte is xored and split at
// s = rho mod 8 by one lookup; the control table pins the one-hot flags that select rho.

use super::*;
use crate::cs::circuit::*;
use crate::definitions::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use core::array::from_fn;

pub use common_constants::delegation_types::keccak_f1600::KECCAK_THETA_RHO_CSR_REGISTER;

pub const KECCAK_RHO_OFFSETS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

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

// low byte committed, high byte affine; the byte lookups range-check both
pub(crate) fn split_bytes<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    limbs: [Variable; 4],
) -> [Expr<F>; 8] {
    let low: [Variable; 4] = from_fn(|_| cs.add_variable());
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let mask = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0xff);
        for m in 0..4 {
            let limb = placer.get_u16(limbs[m]);
            placer.assign_u16(low[m], &limb.and(&mask));
        }
    });
    let inv256 = F::from_u32_unchecked(256).inverse().unwrap();
    from_fn(|k| {
        let m = k / 2;
        if k % 2 == 0 {
            Expr::var(low[m])
        } else {
            (Expr::var(limbs[m]) - Expr::var(low[m])) * Expr::constant(inv256)
        }
    })
}

// three nibbles committed, the fourth affine; the nibble lookups range-check all four
pub(crate) fn split_nibbles<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    limbs: [Variable; 4],
) -> [Expr<F>; 16] {
    let digits: [[Variable; 3]; 4] = from_fn(|_| from_fn(|_| cs.add_variable()));
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let mask = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(15);
        for m in 0..4 {
            let limb = placer.get_u16(limbs[m]);
            for j in 0..3 {
                placer.assign_u16(digits[m][j], &limb.shr(4 * j as u32).and(&mask));
            }
        }
    });
    let inv4096 = F::from_u32_unchecked(4096).inverse().unwrap();
    from_fn(|k| {
        let (m, j) = (k / 4, k % 4);
        if j < 3 {
            Expr::var(digits[m][j])
        } else {
            (Expr::var(limbs[m])
                - Expr::var(digits[m][0])
                - Expr::from(16u32) * Expr::var(digits[m][1])
                - Expr::from(256u32) * Expr::var(digits[m][2]))
                * Expr::constant(inv4096)
        }
    })
}

pub(crate) fn control_register<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) -> (Variable, Variable) {
    let x10 = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: 10,
            register_write: true,
            indirects_alignment_log2: 0,
            indirect_accesses: vec![],
        },
        "x10 control register read/write",
        2,
    );
    let RegisterAccessType::Write {
        read_value: control,
        write_value: control_next,
    } = x10.register_access
    else {
        unreachable!()
    };
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control[1]));
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control_next[1]));
    (control[0], control_next[0])
}

// read-write lanes at `indices` (u64 slots of the x11 state); returns the read and written u16 limbs
pub(crate) fn state_lanes<F: PrimeField, CS: Circuit<F>, const N: usize>(
    cs: &mut CS,
    indices: [Variable; N],
) -> ([[Variable; 4]; N], [[Variable; 4]; N]) {
    let accesses = (0..N)
        .flat_map(|slot| {
            [0, 4].map(|offset_constant| IndirectAccessOffset {
                variable_dependent: Some((core::mem::size_of::<u64>() as u32, indices[slot])),
                offset_constant,
                assume_no_alignment_overflow: true,
                is_write_access: true,
            })
        })
        .collect();
    let x11 = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: 11,
            register_write: false,
            indirects_alignment_log2: 8,
            indirect_accesses: accesses,
        },
        "x11 indirect access",
        2,
    );
    assert_eq!(x11.indirect_accesses.len(), 2 * N);
    let mut lanes_in = [[Variable::placeholder_variable(); 4]; N];
    let mut lanes_out = lanes_in;
    for (word, access) in x11.indirect_accesses.iter().enumerate() {
        let IndirectAccessType::Write {
            read_value,
            write_value,
            ..
        } = *access
        else {
            unreachable!()
        };
        let (slot, half) = (word / 2, word % 2);
        lanes_in[slot][2 * half..2 * half + 2].copy_from_slice(&read_value);
        lanes_out[slot][2 * half..2 * half + 2].copy_from_slice(&write_value);
        cs.set_values(move |placer: &mut CS::WitnessPlacer| {
            if CS::ASSUME_MEMORY_VALUES_ASSIGNED {
                placer.assume_assigned(write_value[0]);
                placer.assume_assigned(write_value[1]);
            } else {
                let value = placer.get_oracle_u32(Placeholder::DelegationIndirectWriteValue {
                    register_index: 11,
                    word_index: word,
                });
                placer.assign_u32_from_u16_parts(write_value, &value);
            }
        });
    }
    (lanes_in, lanes_out)
}

pub(crate) fn tie_unchanged<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    read: [Variable; 4],
    written: [Variable; 4],
) {
    for m in 0..4 {
        cs.add_constraint_expr_allow_explicit_linear(Expr::var(written[m]) - Expr::var(read[m]));
    }
}

pub fn define_keccak_theta_rho_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _invocation_ts) =
        cs.allocate_delegation_state(KECCAK_THETA_RHO_CSR_REGISTER as u16);
    let (control, control_next) = control_register(cs);
    let control_key = Expr::var(control) + Expr::from(1u32 << 11) * Expr::var(execute);

    // 5 lanes, then C[x - 1] and C[x + 1] written back unchanged
    let indices: [Variable; 7] = from_fn(|_| cs.add_variable());
    let (lanes_in, lanes_out) = state_lanes(cs, indices);
    tie_unchanged(cs, lanes_in[5], lanes_out[5]);
    tie_unchanged(cs, lanes_in[6], lanes_out[6]);
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, 8, _>(|i| match i {
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
        let iteration = placer.get_u16(control).shr(3).and(
            &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0b111),
        );
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
                .map(|x| Expr::from(KECCAK_RHO_OFFSETS[x][y] % 8) * Expr::var(flags[x]))
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
                let rotation = KECCAK_RHO_OFFSETS[x][y] as usize;
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
