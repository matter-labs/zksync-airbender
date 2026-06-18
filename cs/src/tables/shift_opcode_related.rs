use super::*;

fn shift_amount_index_fn<F: PrimeField>(keys: &[F]) -> usize {
    let a = keys[0].as_u32_reduced();
    let b = keys[1].as_u32_reduced();

    assert!(a < (1u32 << 8));
    assert!(b < (1u32 << 8));

    ((a << 8) | b) as usize
}

pub fn create_truncate_shift_amount_and_range_check_8_table<F: PrimeField>(
    id: u32,
) -> LookupTable<F> {
    let mut keys = Vec::with_capacity(1 << (8 + 8));
    for first in 0..(1 << 8) {
        for second in 0..(1 << 8) {
            let key = [
                F::from_u32_unchecked(first as u32),
                F::from_u32_unchecked(second as u32),
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Truncate and adjust shift amount");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a < 1 << 8);
            assert!(b < 1 << 8);

            let shift_amount = a & 0b1_1111;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(shift_amount));

            (shift_amount_index_fn::<F>(keys), result)
        },
        Some(shift_amount_index_fn::<F>),
        id,
    )
}

fn shift_implementation_index_fn<F: PrimeField>(keys: &[F]) -> usize {
    let byte_index = keys[0].as_u32_reduced();
    assert!(byte_index < 1 << 2);
    let input_byte = keys[1].as_u32_reduced();
    assert!(input_byte < 1 << 8);
    let shift_amount = keys[2].as_u32_reduced();
    assert!(shift_amount < 1 << 5);
    let funct3 = keys[3].as_u32_reduced();
    assert!(funct3 < 1 << 3);
    ((byte_index << (8 + 5 + 3)) | (input_byte << (5 + 3)) | (shift_amount << 3) | funct3) as usize
}

pub fn create_shift_implementation_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    // byte || shift amount || funct3 || byte index

    let mut keys = Vec::with_capacity(1 << (8 + 5 + 3 + 2));

    for input_byte_idx in 0..(1 << 2) {
        for byte in 0..(1 << 8) {
            for shift in 0..(1 << 5) {
                for funct3 in 0..(1 << 3) {
                    let key = [
                        F::from_u32_unchecked(input_byte_idx as u32),
                        F::from_u32_unchecked(byte as u32),
                        F::from_u32_unchecked(shift as u32),
                        F::from_u32_unchecked(funct3 as u32),
                    ];
                    keys.push(key)
                }
            }
        }
    }

    let table_name = "Shift implementation over bytes table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        4,
        4,
        |keys| {
            let byte_index = keys[0].as_u32_reduced();
            assert!(byte_index < 1 << 2);
            let input_byte = keys[1].as_u32_reduced();
            assert!(input_byte < 1 << 8);
            let shift_amount = keys[2].as_u32_reduced();
            assert!(shift_amount < 1 << 5);
            let funct3 = keys[3].as_u32_reduced();
            assert!(funct3 < 1 << 3);
            let funct3 = funct3 as u8;

            let mut out_value = 0u32;
            let input_value = input_byte << (byte_index * 8);

            use crate::gkr_circuits::binary_shifts_family::{
                FORMAL_ROL_FUNCT3, FORMAL_ROR_FUNCT3, FORMAL_SLL_FUNCT3, FORMAL_SRA_FUNCT3,
                FORMAL_SRL_FUNCT3,
            };

            match funct3 {
                FORMAL_SLL_FUNCT3 => {
                    out_value = input_value << shift_amount;
                }
                FORMAL_SRL_FUNCT3 => {
                    out_value = input_value >> shift_amount;
                }
                FORMAL_SRA_FUNCT3 => {
                    // NOTE: same expression for both highest and not byte,
                    // as if byte is not highest then top bit is not set and SRA is equal to SRL
                    out_value = ((input_value as i32) >> shift_amount) as u32;
                }
                _ => {}
            }

            let out_bytes = out_value.to_le_bytes();
            let mut result = ArrayVec::new();
            for b in out_bytes.into_iter() {
                result.push(F::from_u32_unchecked(b as u32));
            }

            (shift_implementation_index_fn::<F>(keys), result)
        },
        Some(shift_implementation_index_fn::<F>),
        id,
    )
}
