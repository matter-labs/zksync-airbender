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
                FORMAL_BSWAP_FUNCT3, FORMAL_ROL_FUNCT3, FORMAL_ROR_FUNCT3, FORMAL_SLL_FUNCT3,
                FORMAL_SRA_FUNCT3, FORMAL_SRL_FUNCT3,
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
                FORMAL_BSWAP_FUNCT3 => {
                    // byte `i` goes to byte `3 - i`; the decoder pins the shift amount to 0, so
                    // rows with a non-zero amount are unreachable and left zero
                    if shift_amount == 0 {
                        out_value = input_byte << ((3 - byte_index) * 8);
                    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_circuits::binary_shifts_family::{FORMAL_BSWAP_FUNCT3, FORMAL_SRL_FUNCT3};
    use field::baby_bear::base::BabyBearField;

    type F = BabyBearField;

    /// Replays the circuit's shift-path reconstruction for byte swap: one lookup per byte
    /// `(i, rs1_byte[i], 0, BSWAP)`, chunks summed slot-wise into 4 output bytes. Every slot
    /// must receive exactly one byte, so the result is canonical and equals `swap_bytes`.
    #[test]
    fn byte_swap_rows_reconstruct_swap_bytes() {
        let table = create_shift_implementation_table::<F>(1);
        let words = [
            0u32,
            u32::MAX,
            0xDDCC_BBAA,
            0x0000_AA00,
            0xAA00_0000,
            0x0102_0304,
            0x8000_0001,
        ];
        for word in words {
            let mut out = [0u32; 4];
            for (i, byte) in word.to_le_bytes().into_iter().enumerate() {
                let keys = [
                    F::from_u32_unchecked(i as u32),
                    F::from_u32_unchecked(byte as u32),
                    F::from_u32_unchecked(0),
                    F::from_u32_unchecked(FORMAL_BSWAP_FUNCT3 as u32),
                ];
                let chunk: [F; 4] = table.lookup_value::<4>(&keys);
                let nonzero_slots = chunk.iter().filter(|c| c.as_u32_reduced() != 0).count();
                assert!(
                    nonzero_slots <= 1,
                    "byte {i} of {word:#010x} split across slots"
                );
                for (slot, c) in chunk.iter().enumerate() {
                    out[slot] += c.as_u32_reduced();
                }
            }
            assert!(out.iter().all(|&b| b <= u8::MAX as u32));
            let got = u32::from_le_bytes(out.map(|b| b as u8));
            assert_eq!(got, word.swap_bytes(), "bswap({word:#010x})");
        }
    }

    /// The BSWAP arm must not disturb existing shift rows (spot-check SRL next to it).
    #[test]
    fn byte_swap_code_is_distinct_from_existing_shifts() {
        let table = create_shift_implementation_table::<F>(1);
        let keys = |funct3: u8| {
            [
                F::from_u32_unchecked(3),
                F::from_u32_unchecked(0xAB),
                F::from_u32_unchecked(4),
                F::from_u32_unchecked(funct3 as u32),
            ]
        };
        let srl: [F; 4] = table.lookup_value::<4>(&keys(FORMAL_SRL_FUNCT3));
        let expected = (0xABu32 << 24) >> 4;
        let srl_word = u32::from_le_bytes(srl.map(|c| c.as_u32_reduced() as u8));
        assert_eq!(srl_word, expected);
        // Unreachable BSWAP rows (non-zero shift amount) stay zero.
        let bswap: [F; 4] = table.lookup_value::<4>(&keys(FORMAL_BSWAP_FUNCT3));
        assert!(bswap.iter().all(|c| c.as_u32_reduced() == 0));
    }
}
