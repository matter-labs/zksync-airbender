use super::*;

pub fn create_xor_table<F: PrimeField, const WIDTH: usize>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation_for_width::<F, 2, WIDTH>();
    let table_name = format!("XOR {}x{} bit table", WIDTH, WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();

            assert!(
                a < 1u32 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                a,
                WIDTH
            );
            assert!(
                b < 1u32 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                b,
                WIDTH
            );

            let binop_result = a ^ b;
            let value = binop_result as u32;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(value));

            (index_for_binary_key_for_width::<WIDTH>(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, WIDTH>),
        id,
    )
}

pub fn create_and_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    const TABLE_NAME: &'static str = "AND table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();

            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);

            let binop_result = a & b;
            let value = binop_result as u32;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(value));

            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

pub fn create_or_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    const TABLE_NAME: &'static str = "OR table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();

            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);

            let binop_result = a | b;
            let value = binop_result as u32;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(value));

            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

pub fn create_and_not_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    const TABLE_NAME: &'static str = "AND NOT table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();

            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);

            let binop_result = a & (!b);
            let value = binop_result as u32;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(value));

            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

pub fn create_sign_extension_byte_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_for_continuous_log2_range::<F, 1>(8);
    const TABLE_NAME: &'static str = "Sign extension byte for binops immediate table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let input_sign = (a >> 7) > 0;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked((input_sign as u32) * 0xff));

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}
