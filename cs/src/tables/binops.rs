use super::*;

pub fn create_xor_table<F: PrimeField, const WIDTH: usize>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation_for_width::<F, 3, WIDTH>();
    let table_name = format!("XOR {}x{} bit table", WIDTH, WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(
                a < 1u64 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                a,
                WIDTH
            );
            assert!(
                b < 1u64 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                b,
                WIDTH
            );

            let binop_result = a ^ b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key_for_width::<WIDTH>(a, b), result)
        },
        Some(bit_chunks_index_gen_fn::<F, 3, WIDTH>),
        id,
    )
}

pub fn create_and_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "AND table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a & b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_or_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "OR table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a | b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_and_not_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "AND NOT table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a & (!b);
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}
