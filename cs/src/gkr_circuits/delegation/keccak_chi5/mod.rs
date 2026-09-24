//! Keccak chi on a whole plane: five read-write lanes, 16 shared nibble lookups.
use super::*;
use crate::cs::circuit::*;
use crate::definitions::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::{LookupTable, LookupWrapper};
use crate::witness_placer::*;
use common_constants::delegation_types::keccak_k2::KECCAK_CHI5_CSR_REGISTER;
use core::array::from_fn;

pub const CHI5_TABLE_TYPES: [TableType; 2] = [TableType::KeccakChi5, TableType::KeccakChi5Control];

fn chi5_control(round: usize, plane: usize) -> u16 {
    assert!(round < 24 && plane < 5);
    (5 + 8 * plane + 64 * round) as u16
}

fn chi5_next_control(round: usize, plane: usize) -> u16 {
    if plane == 4 {
        (64 * (round + 1)) as u16
    } else {
        chi5_control(round, plane + 1)
    }
}

// physical slots of `plane` after `round + 1` pi relabelings
fn chi5_indices(round: usize, plane: usize) -> [u16; 5] {
    assert!(round < 24 && plane < 5);
    let mut physical: [u16; 25] = from_fn(|i| i as u16);
    for _ in 0..=round {
        let previous = physical;
        for y in 0..5 {
            for x in 0..5 {
                physical[y + 5 * ((2 * x + 3 * y) % 5)] = previous[x + 5 * y];
            }
        }
    }
    from_fn(|x| physical[5 * plane + x])
}

fn chi_table<F: PrimeField>() -> LookupWrapper<F> {
    let keys: Vec<[F; 5]> = (0..1u32 << 20)
        .map(|key| from_fn(|i| F::from_u32_unchecked((key >> (4 * i)) & 15)))
        .collect();
    LookupWrapper::Initialized(LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Keccak chi five nibbles".to_owned(),
        5,
        5,
        |key| {
            let n: [u32; 5] = from_fn(|i| key[i].as_u32_reduced());
            let index = (0..5).fold(0, |acc, i| acc | ((n[i] as usize) << (4 * i)));
            let output = (0..5)
                .map(|i| F::from_u32_unchecked(n[i] ^ (!n[(i + 1) % 5] & n[(i + 2) % 5])))
                .collect();
            (index, output)
        },
        Some(|key| {
            (0..5).fold(0, |acc, i| {
                acc | ((key[i].as_u32_reduced() as usize) << (4 * i))
            })
        }),
        TableType::KeccakChi5 as u32,
    ))
}

fn control_table<F: PrimeField>() -> LookupWrapper<F> {
    let mut keys = vec![[F::ZERO]];
    for round in 0..24 {
        for plane in 0..5 {
            keys.push([F::from_u32_unchecked(
                2048 + chi5_control(round, plane) as u32,
            )]);
        }
    }
    LookupWrapper::Initialized(LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Keccak chi control and five indices".to_owned(),
        1,
        6,
        |key| {
            let control = key[0].as_u32_reduced() as usize;
            if control == 0 {
                return (0, [F::ZERO; 6].into_iter().collect());
            }
            let round = (control & 2047) >> 6;
            let plane = (control >> 3) & 7;
            let mut output = arrayvec::ArrayVec::new();
            output.push(F::from_u32_unchecked(chi5_next_control(round, plane) as u32));
            output.extend(chi5_indices(round, plane).map(|i| F::from_u32_unchecked(i as u32)));
            (1 + round * 5 + plane, output)
        },
        Some(|key| {
            let control = key[0].as_u32_reduced() as usize;
            if control == 0 {
                0
            } else {
                1 + ((control & 2047) >> 6) * 5 + ((control >> 3) & 7)
            }
        }),
        TableType::KeccakChi5Control as u32,
    ))
}

pub fn keccak_chi5_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    cs.add_table_with_content(TableType::KeccakChi5, chi_table());
    cs.add_table_with_content(TableType::KeccakChi5Control, control_table());
}

pub fn keccak_chi5_table_driver_fn<F: PrimeField>(driver: &mut TableDriver<F>) {
    driver.add_table_with_content(TableType::KeccakChi5, chi_table());
    driver.add_table_with_content(TableType::KeccakChi5Control, control_table());
}

fn nibble_limbs<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, limbs: [Variable; 4]) -> [Expr<F>; 16] {
    let digits: [[Variable; 3]; 4] = from_fn(|_| from_fn(|_| cs.add_variable()));
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        for k in 0..4 {
            let value = placer.get_u16(limbs[k]);
            for j in 0..3 {
                let digit = value
                    .shr((4 * j) as u32)
                    .and(&<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(15));
                placer.assign_u16(digits[k][j], &digit);
            }
        }
    });
    let inv4096 = F::from_u32_unchecked(4096).inverse().unwrap();
    from_fn(|i| {
        let k = i / 4;
        if i % 4 < 3 {
            Expr::var(digits[k][i % 4])
        } else {
            (Expr::var(limbs[k])
                - Expr::var(digits[k][0])
                - Expr::from(16u32) * Expr::var(digits[k][1])
                - Expr::from(256u32) * Expr::var(digits[k][2]))
                * Expr::constant(inv4096)
        }
    })
}

pub fn define_keccak_chi5_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    let (execute, _) = cs.allocate_delegation_state(KECCAK_CHI5_CSR_REGISTER as u16);
    let control = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: 10,
            register_write: true,
            indirects_alignment_log2: 0,
            indirect_accesses: vec![],
        },
        "chi control",
        2,
    );
    let RegisterAccessType::Write {
        read_value: control_in,
        write_value: control_out,
    } = control.register_access
    else {
        unreachable!()
    };
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control_in[1]));
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control_out[1]));
    let indices: [Variable; 5] = from_fn(|_| cs.add_variable());
    let accesses = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: 11,
            register_write: false,
            indirects_alignment_log2: 8,
            indirect_accesses: indices
                .into_iter()
                .flat_map(|index| {
                    (0..2).map(move |half| IndirectAccessOffset {
                        variable_dependent: Some((8, index)),
                        offset_constant: 4 * half,
                        assume_no_alignment_overflow: true,
                        is_write_access: true,
                    })
                })
                .collect(),
        },
        "chi state",
        2,
    );
    let control_tuple: [LookupInput<F>; 7] = from_fn(|i| match i {
        0 => LookupInput::from(Expr::var(control_in[0]) + Expr::from(2048u32) * Expr::var(execute)),
        1 => LookupInput::from(control_out[0]),
        _ => LookupInput::from(indices[i - 2]),
    });
    cs.enforce_lookup_tuple_for_fixed_table(&control_tuple, TableType::KeccakChi5Control, false);
    let mut input = [[Variable::placeholder_variable(); 4]; 5];
    let mut output = input;
    for (word, access) in accesses.indirect_accesses.iter().enumerate() {
        let IndirectAccessType::Write {
            read_value,
            write_value,
            ..
        } = *access
        else {
            unreachable!()
        };
        input[word / 2][2 * (word % 2)..2 * (word % 2) + 2].copy_from_slice(&read_value);
        output[word / 2][2 * (word % 2)..2 * (word % 2) + 2].copy_from_slice(&write_value);
        cs.set_values(move |placer: &mut CS::WitnessPlacer| {
            if CS::ASSUME_MEMORY_VALUES_ASSIGNED {
                for var in write_value {
                    placer.assume_assigned(var);
                }
            } else {
                let value = placer.get_oracle_u32(Placeholder::DelegationIndirectWriteValue {
                    register_index: 11,
                    word_index: word,
                });
                placer.assign_u32_from_u16_parts(write_value, &value);
            }
        });
    }
    let input = input.map(|limbs| nibble_limbs(cs, limbs));
    let output = output.map(|limbs| nibble_limbs(cs, limbs));
    for digit in 0..16 {
        let tuple: [LookupInput<F>; 10] = from_fn(|i| {
            LookupInput::from(if i < 5 {
                input[i][digit].clone()
            } else {
                output[i - 5][digit].clone()
            })
        });
        cs.enforce_lookup_tuple_for_fixed_table(&tuple, TableType::KeccakChi5, false);
    }
}

#[cfg(test)]
mod tests;
