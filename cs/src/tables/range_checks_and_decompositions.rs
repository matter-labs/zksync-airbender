use super::*;

pub fn create_quick_decoder_decomposition_table_4x4x4<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (4 + 4 + 4));
    let u4_max = 0x0f as u8;
    for a in 0..=u4_max {
        for b in 0..=u4_max {
            for c in 0..=u4_max {
                let row = [
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64),
                    F::from_u64_unchecked(c as u64),
                ];
                keys.push(row);
            }
        }
    }

    const TABLE_NAME: &'static str = "quick decoder decomposition 4x4x4 table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            let c = keys[2].as_u64_reduced();

            assert!(a < (1u64 << 4));
            assert!(b < (1u64 << 4));
            assert!(c < (1u64 << 4));

            let index = (a << 8) | (b << 4) | c;

            (index as usize, [F::ZERO; 3])
        },
        None,
        id,
    )
}

pub fn create_quick_decoder_decomposition_table_7x3x6<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (7 + 3 + 6));
    let u7_max = 0b0111_1111 as u8;
    let u3_max = 0b0111 as u8;
    let u6_max = 0b0011_1111 as u8;
    for a in 0..=u7_max {
        for b in 0..=u3_max {
            for c in 0..=u6_max {
                let row = [
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64),
                    F::from_u64_unchecked(c as u64),
                ];
                keys.push(row);
            }
        }
    }
    assert_eq!(keys.len(), 1 << (7 + 3 + 6));

    const TABLE_NAME: &'static str = "quick decoder decomposition 7x3x6 table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            let c = keys[2].as_u64_reduced();

            assert!(a < (1u64 << 7));
            assert!(b < (1u64 << 3));
            assert!(c < (1u64 << 6));

            let index = (a << 9) | (b << 6) | c;

            (index as usize, [F::ZERO; 3])
        },
        None,
        id,
    )
}

pub fn create_u16_get_sign_and_high_byte_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "U16 get sign and high byte table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16), "input value is 0x{:08x}", a);

            let sign = a >> 15;
            let high_byte = a >> 8;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(sign as u64);
            result[1] = F::from_u64_unchecked(high_byte as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_range_check_table<F: PrimeField, const M: usize>(id: u32) -> LookupTable<F, 1> {
    assert!(M > 0);
    let keys = key_for_continuous_log2_range(M);
    let table_name = format!("Range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << M));

            (a as usize, [F::ZERO])
        },
        Some(first_key_index_gen_fn::<F, 1>),
        id,
    )
}

pub fn create_formal_width_3_range_check_table_for_two_tuple<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F, 3> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << (M * 2));
    for first in 0..(1 << M) {
        for second in 0..(1 << M) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));
            assert!(b < (1u64 << M));

            (((a << M) | b) as usize, [F::ZERO; 3])
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));
            assert!(b < (1u64 << M));

            ((a << M) | b) as usize
        }),
        id,
    )
}

pub fn create_formal_width_3_range_check_table_for_single_entry<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F, 3> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << M);
    for first in 0..(1 << M) {
        let key = [F::from_u64_unchecked(first as u64), F::ZERO, F::ZERO];
        keys.push(key)
    }
    let table_name = format!("Width-3 range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(keys[1].is_zero());
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));

            (a as usize, [F::ZERO; 3])
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            assert!(keys[1].is_zero());
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));

            a as usize
        }),
        id,
    )
}

pub fn create_select_byte_and_get_sign_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // This table takes a word + single bit, and selected a byte + gets sign on the byte
    let keys = key_for_continuous_log2_range(16 + 1);

    let table_name = "Select byte and get sign table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < 1 << 17);

            let word = a as u16;
            let selector_bit = (a >> 16) != 0;

            let selected_byte = if selector_bit {
                (word >> 8) as u8
            } else {
                word as u8
            };

            let sign_bit = selected_byte & (1 << 7) != 0;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(selected_byte as u64);
            result[1] = F::from_boolean(sign_bit);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_u16_split_into_bytes_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "U16 split into bytes table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let low_byte = a & 0xff;
            let high_byte = a >> 8;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(low_byte as u64);
            result[1] = F::from_u64_unchecked(high_byte as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
