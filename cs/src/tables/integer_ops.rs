use super::*;

pub fn create_u16_get_sign_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_for_continuous_log2_range::<F, 1>(16);
    const TABLE_NAME: &'static str = "U16 get sign table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << 16), "input value is 0x{:08x}", a);

            let sign = a >> 15;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(sign));

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}

pub fn create_reg_is_zero_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_for_continuous_log2_range::<F, 1>(17);
    const TABLE_NAME: &'static str = "Reg is zero table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << 17), "input value is 0x{:08x}", a);

            let is_zero = a == 0;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(is_zero as u32));

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}

pub fn create_range_check_table_for_two_tuple<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << (M * 2));
    for first in 0..(1 << M) {
        for second in 0..(1 << M) {
            let key = [
                F::from_u32_unchecked(first as u32),
                F::from_u32_unchecked(second as u32),
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        0,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a < (1u32 << M));
            assert!(b < (1u32 << M));

            (((a << M) | b) as usize, ArrayVec::new())
        },
        Some(|keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a < (1u32 << M));
            assert!(b < (1u32 << M));

            ((a << M) | b) as usize
        }),
        id,
    )
}

pub fn create_range_check_table_for_single_entry<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << M);
    for first in 0..(1 << M) {
        let key = [F::from_u32_unchecked(first as u32)];
        keys.push(key)
    }
    let table_name = format!("Width-3 range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        0,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << M));

            (a as usize, ArrayVec::new())
        },
        Some(|keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << M));

            a as usize
        }),
        id,
    )
}

pub fn create_u16_get_low_byte_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_for_continuous_log2_range::<F, 1>(16);
    const TABLE_NAME: &'static str = "U16 get low byte table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << 16), "input value is 0x{:08x}", a);

            let low = a as u8;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(low as u32));

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}
