// Chi (precompile code 5), iteration x: the five lanes of plane x after the round's pi relabeling;
// every 4-bit slice of the plane goes through one five-nibble chi lookup.

use super::keccak_f1600_gadgets::{control_key, control_register, split_nibbles, state_lanes};
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
    let (lanes_in, lanes_out) = state_lanes(cs, indices);
    cs.enforce_lookup_tuple_for_fixed_table(
        &from_fn::<_, { KECCAK_CHI5_NUM_VARIABLE_OFFSETS + 2 }, _>(|i| match i {
            0 => LookupInput::from(control_key(control, execute)),
            1 => LookupInput::from(control_next),
            _ => LookupInput::from(indices[i - 2]),
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
