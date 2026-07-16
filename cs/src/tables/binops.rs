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

pub fn create_xor_rotate_table<F: PrimeField, const ROT: u32>(id: u32) -> LookupTable<F> {
    const {
        assert!(
            ROT < 32,
            "ROT must be a valid u32 rotate-right amount (< 32)"
        )
    };
    let keys = key_binary_generation::<F, 2>();
    let table_name = format!("XOR-rotate-right-{} table", ROT);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        4,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);

            let z = a ^ b; // XOR'd byte, sits at byte 0
            let rotated = z.rotate_right(ROT);
            let mut result = ArrayVec::new();
            for byte in rotated.to_le_bytes().into_iter() {
                result.push(F::from_u32_unchecked(byte as u32));
            }
            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

/// Unified-only 4-output zero-padded XOR table: (a, b) -> (a ^ b, 0, 0, 0).
/// Output shape matches `create_xor_rotate_table` at rotation 0 so plain binops and
/// xor-rotate share one lookup shape + cyclic byte reconstruction in the unified circuit.
pub fn create_wide_xor_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Wide XOR table".to_string(),
        2,
        4,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(a ^ b));
            for _ in 0..3 {
                result.push(F::from_u32_unchecked(0));
            }
            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

/// Unified-only 4-output zero-padded OR table: (a, b) -> (a | b, 0, 0, 0). See `create_wide_xor_table`.
pub fn create_wide_or_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Wide OR table".to_string(),
        2,
        4,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(a | b));
            for _ in 0..3 {
                result.push(F::from_u32_unchecked(0));
            }
            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
        id,
    )
}

/// Unified-only 4-output zero-padded AND table: (a, b) -> (a & b, 0, 0, 0). See `create_wide_xor_table`.
pub fn create_wide_and_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_binary_generation::<F, 2>();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Wide AND table".to_string(),
        2,
        4,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            assert!(a <= u8::MAX as u32);
            assert!(b <= u8::MAX as u32);
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(a & b));
            for _ in 0..3 {
                result.push(F::from_u32_unchecked(0));
            }
            (index_for_binary_key(a, b), result)
        },
        Some(bit_chunks_slice_index_gen_fn::<F, 8>),
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

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField;

    type F = BabyBearField;

    /// The Wide{Xor,Or,And} tables must be exactly "narrow output + 3 zero columns", and
    /// WideXor must coincide row-for-row with XorRotate at rotation 0 — that identity is
    /// what lets the unified circuit run plain binops through the xor-rotate cyclic
    /// reconstruction (rot-0 ⇒ identity byte placement).
    #[test]
    fn wide_binop_tables_shape() {
        let wide_xor = create_wide_xor_table::<F>(1);
        let wide_or = create_wide_or_table::<F>(2);
        let wide_and = create_wide_and_table::<F>(3);
        let xor_rot_0 = create_xor_rotate_table::<F, 0>(4);
        let narrow_xor = create_xor_table::<F, 8>(5);
        let narrow_or = create_or_table::<F>(6);
        let narrow_and = create_and_table::<F>(7);

        let zero = F::from_u32_unchecked(0);
        let samples: [(u32, u32); 6] = [
            (0, 0),
            (255, 255),
            (0x5A, 0xA5),
            (1, 0),
            (0, 128),
            (0x0F, 0xF0),
        ];
        for (a, b) in samples {
            let keys = [F::from_u32_unchecked(a), F::from_u32_unchecked(b)];
            for (wide, narrow, opname) in [
                (&wide_xor, &narrow_xor, "xor"),
                (&wide_or, &narrow_or, "or"),
                (&wide_and, &narrow_and, "and"),
            ] {
                let wide_row: [F; 4] = wide.lookup_value::<4>(&keys);
                let narrow_row: [F; 1] = narrow.lookup_value::<1>(&keys);
                assert_eq!(wide_row[0], narrow_row[0], "{opname}({a:#x},{b:#x}) output");
                assert_eq!(
                    &wide_row[1..],
                    &[zero; 3],
                    "{opname}({a:#x},{b:#x}) padding must be zero"
                );
            }
            // WideXor == XorRotate<0> row-for-row (rot-0 identity placement).
            assert_eq!(
                wide_xor.lookup_value::<4>(&keys),
                xor_rot_0.lookup_value::<4>(&keys),
                "WideXor must equal XorRotate rot-0 for ({a:#x},{b:#x})"
            );
        }
    }
}
