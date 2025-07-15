use super::*;

pub fn create_sra_sign_filler_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(1 + 1 + 5);
    const TABLE_NAME: &'static str = "SRA sign bits filler table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let input_sign = a & 1 > 0;
            let is_sra = (a >> 1) & 1 > 0;
            let shift_amount = a >> 2;
            assert!(shift_amount < 32);

            if input_sign == false || is_sra == false {
                // either it's positive, or we are not doing SRA (and it's actually the only case when shift amount can be >= 32
                // in practice, but we have to fill the table)
                let result = [F::ZERO; 3];

                (a as usize, result)
            } else {
                if shift_amount == 0 {
                    // special case
                    let result = [F::ZERO; 3];

                    (a as usize, result)
                } else {
                    let (mask, _) = u32::MAX.overflowing_shl(32 - (shift_amount as u32));

                    let mut result = [F::ZERO; 3];
                    result[0] = F::from_u64_unchecked(mask as u16 as u64);
                    result[1] = F::from_u64_unchecked((mask >> 16) as u16 as u64);

                    (a as usize, result)
                }
            }
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_shift_implementation_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // take 16 bits of input half-word || shift || is_right

    let keys = key_for_continuous_log2_range(16 + 5 + 1);

    let table_name = "Shift implementation table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let input_word = a as u16;
            let shift_amount = ((a >> 16) & 0b1_1111) as u32;
            let is_right_shift = (a >> (16 + 5)) > 0;

            let (in_place, overflow) = if is_right_shift {
                let input = (input_word as u32) << 16;
                let t = input >> shift_amount;
                let in_place = (t >> 16) as u16;
                let overflow = t as u16;

                (in_place, overflow)
            } else {
                let input = input_word as u32;
                let t = input << shift_amount;
                let in_place = t as u16;
                let overflow = (t >> 16) as u16;

                (in_place, overflow)
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(in_place as u64);
            result[1] = F::from_u64_unchecked(overflow as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_truncate_shift_amount_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (8 + 1));
    for first in 0..(1 << 8) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Truncate and adjust shift amount");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(a < 1 << 8);

            let is_right_shift = b != 0;
            let shift_amount = a & 0b1_1111;
            let shift_amount = if is_right_shift {
                shift_amount
            } else {
                32 - shift_amount
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(shift_amount as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 8));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_shift_amount_truncation_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 16;

    let keys = key_for_continuous_log2_range(TABLE_WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        format!("Shift amount truncation table"),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1 << TABLE_WIDTH));

            let shift_amount = a & 0b11111;

            let result = [F::from_u64_unchecked(shift_amount as u64), F::ZERO, F::ZERO];
            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_logical_shift_16_bit_table<
    F: PrimeField,
    const INPUT_IS_HIGH: bool,
    const IS_RIGHT_SHIFT: bool,
>(
    id: u32,
) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 16 + 5;

    let keys = key_for_continuous_log2_range(TABLE_WIDTH);

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        format!(
            "Logical shift table: high input word = {}, is right shift = {}",
            INPUT_IS_HIGH, IS_RIGHT_SHIFT
        ),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1 << TABLE_WIDTH));

            let word = (a & 0xffff) as u32;
            let shift_amount = a >> 16;

            let reconstructed = if INPUT_IS_HIGH { word << 16 } else { word };

            let shift_result = if IS_RIGHT_SHIFT {
                reconstructed >> shift_amount
            } else {
                reconstructed << shift_amount
            };

            let low_result = shift_result & 0xffff;
            let high_result = shift_result >> 16;

            let result = [
                F::from_u64_unchecked(low_result as u64),
                F::from_u64_unchecked(high_result as u64),
                F::ZERO,
            ];
            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_sra_16_filler_mask_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 16 + 5;

    let keys = key_for_continuous_log2_range(TABLE_WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        format!("SRA filler bits table"),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1 << TABLE_WIDTH));

            let word = (a & 0xffff) as u32;
            let shift_amount = ((a >> 16) & 0b11111) as u32;
            let sign_bit = (word >> 15) != 0;

            // we have top word
            let mask = if sign_bit {
                // there is no mask if we shift by 0,
                // otherwise - it's some number of top bits being 1s
                u32::MAX.wrapping_shr(32 - shift_amount)
            } else {
                0u32
            };

            let low_result = mask & 0xffff;
            let high_result = mask >> 16;

            let result = [
                F::from_u64_unchecked(low_result as u64),
                F::from_u64_unchecked(high_result as u64),
                F::ZERO,
            ];
            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
