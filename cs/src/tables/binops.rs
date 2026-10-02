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

/// Number of values of the `carry` column in `create_xor_with_carry_table`: carry out of a
/// 16-bit limb in addition of three 16-bit values and a carry in is one of {0, 1, 2}
pub const XOR_WITH_CARRY_NUM_CARRY_VALUES: u32 = 3;

// index in the table is (carry << (2 * WIDTH)) || (key0 << WIDTH) || key1, so it is a plain
// concatenation of bits as for the other binary tables
fn index_for_xor_with_carry_key<const WIDTH: usize>(a: u32, b: u32, carry: u32) -> usize {
    ((carry as usize) << (2 * WIDTH)) | index_for_binary_key_for_width::<WIDTH>(a, b)
}

/// Row index from the full row. Unlike the index functions of the plain binary tables it also
/// checks the value column, so `lookup_enforce` over a row that is not in the table panics.
fn xor_with_carry_index_gen_fn<F: PrimeField, const WIDTH: usize>(row: &[F]) -> usize {
    assert!(row.len() >= 3);
    let a = row[0].as_u32_reduced();
    let b = row[1].as_u32_reduced();
    let carry = row[2].as_u32_reduced();

    assert!(a < 1u32 << WIDTH);
    assert!(b < 1u32 << WIDTH);
    assert!(carry < XOR_WITH_CARRY_NUM_CARRY_VALUES);
    if let Some(value) = row.get(3) {
        assert_eq!(value.as_u32_reduced(), a ^ b);
    }

    index_for_xor_with_carry_key::<WIDTH>(a, b, carry)
}

/// XOR table with an extra key column that is only range checked:
/// (a, b, carry) -> a ^ b for `WIDTH`-bit `a` and `b`, and `carry` in {0, 1, 2}.
///
/// The `carry` column lets a lookup that is needed anyway also range check a carry of
/// 16-bit limb addition, so the carry needs neither two boolean columns nor its own lookup.
pub fn create_xor_with_carry_table<F: PrimeField, const WIDTH: usize>(id: u32) -> LookupTable<F> {
    let len = (XOR_WITH_CARRY_NUM_CARRY_VALUES as usize) << (WIDTH * 2);
    let mut keys = Vec::with_capacity(len);
    for carry in 0..XOR_WITH_CARRY_NUM_CARRY_VALUES {
        for a in 0..(1u32 << WIDTH) {
            for b in 0..(1u32 << WIDTH) {
                keys.push([
                    F::from_u32_unchecked(a),
                    F::from_u32_unchecked(b),
                    F::from_u32_unchecked(carry),
                ]);
            }
        }
    }
    assert_eq!(keys.len(), len);

    let table_name = format!("XOR {}x{} bit table with carry column", WIDTH, WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            let carry = keys[2].as_u32_reduced();

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
            assert!(
                carry < XOR_WITH_CARRY_NUM_CARRY_VALUES,
                "carry {} is too large",
                carry
            );

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(a ^ b));

            (index_for_xor_with_carry_key::<WIDTH>(a, b, carry), result)
        },
        Some(xor_with_carry_index_gen_fn::<F, WIDTH>),
        id,
    )
}

fn index_for_xor_4x3_key(a4: u32, a3: u32, b4: u32, b3: u32) -> usize {
    ((a4 << 10) | (a3 << 7) | (b4 << 3) | b3) as usize
}

/// Row index from the full row, also checks the value column (see `xor_with_carry_index_gen_fn`).
fn xor_4x3_index_gen_fn<F: PrimeField>(row: &[F]) -> usize {
    assert!(row.len() >= 4);
    let a4 = row[0].as_u32_reduced();
    let a3 = row[1].as_u32_reduced();
    let b4 = row[2].as_u32_reduced();
    let b3 = row[3].as_u32_reduced();

    assert!(a4 < 1 << 4);
    assert!(a3 < 1 << 3);
    assert!(b4 < 1 << 4);
    assert!(b3 < 1 << 3);
    if let Some(value) = row.get(4) {
        assert_eq!(value.as_u32_reduced(), (a4 ^ b4) | ((a3 ^ b3) << 4));
    }

    index_for_xor_4x3_key(a4, a3, b4, b3)
}

/// XOR of two 7-bit values, each given as a 4-bit and a 3-bit piece in separate columns:
/// (a4, a3, b4, b3) -> (a4 ^ b4) + 16 * (a3 ^ b3).
///
/// Every piece is range checked by its own column, so the pieces can come from different
/// decompositions (in Blake2s - from two different 16-bit limbs), while the output is a
/// single 7-bit value.
pub fn create_xor_4x3_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let len = 1usize << 14;
    let mut keys = Vec::with_capacity(len);
    for a4 in 0..(1u32 << 4) {
        for a3 in 0..(1u32 << 3) {
            for b4 in 0..(1u32 << 4) {
                for b3 in 0..(1u32 << 3) {
                    keys.push([
                        F::from_u32_unchecked(a4),
                        F::from_u32_unchecked(a3),
                        F::from_u32_unchecked(b4),
                        F::from_u32_unchecked(b3),
                    ]);
                }
            }
        }
    }
    assert_eq!(keys.len(), len);

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "XOR (4+3)x(4+3) bit table".to_string(),
        4,
        1,
        |keys| {
            let a4 = keys[0].as_u32_reduced();
            let a3 = keys[1].as_u32_reduced();
            let b4 = keys[2].as_u32_reduced();
            let b3 = keys[3].as_u32_reduced();

            assert!(a4 < 1 << 4, "input 0x{:08x} is too large for 4 bits", a4);
            assert!(a3 < 1 << 3, "input 0x{:08x} is too large for 3 bits", a3);
            assert!(b4 < 1 << 4, "input 0x{:08x} is too large for 4 bits", b4);
            assert!(b3 < 1 << 3, "input 0x{:08x} is too large for 3 bits", b3);

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked((a4 ^ b4) | ((a3 ^ b3) << 4)));

            (index_for_xor_4x3_key(a4, a3, b4, b3), result)
        },
        Some(xor_4x3_index_gen_fn::<F>),
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

    /// Row index reported by the generation function and by the index function must be the
    /// position of the row in the table, and the index function must reject wrong outputs.
    #[test]
    fn blake_round_function_wide_tables_shape() {
        fn check(table: &LookupTable<F>, size: usize) {
            assert_eq!(table.table_size(), size);
            for (idx, row) in table.data.iter().enumerate() {
                assert_eq!(table.lookup_row(&row[..]), idx);
                let (index, _) = table.lookup_values_and_get_index::<1>(&row[..table.num_keys()]);
                assert_eq!(index, idx);
            }
        }

        let xor_8_with_carry = create_xor_with_carry_table::<F, 8>(1);
        check(&xor_8_with_carry, 3 << 16);
        let xor_7_with_carry = create_xor_with_carry_table::<F, 7>(2);
        check(&xor_7_with_carry, 3 << 14);
        let xor_4x3 = create_xor_4x3_table::<F>(3);
        check(&xor_4x3, 1 << 14);

        let f = F::from_u32_unchecked;
        // carry does not affect the output
        for carry in 0..XOR_WITH_CARRY_NUM_CARRY_VALUES {
            assert_eq!(
                xor_8_with_carry.lookup_value::<1>(&[f(0x5a), f(0xa3), f(carry)]),
                [f(0x5a ^ 0xa3)]
            );
            assert_eq!(
                xor_7_with_carry.lookup_value::<1>(&[f(0x5a), f(0x23), f(carry)]),
                [f(0x5a ^ 0x23)]
            );
        }
        // (a4, a3, b4, b3) -> (a4 ^ b4) + 16 * (a3 ^ b3)
        assert_eq!(
            xor_4x3.lookup_value::<1>(&[f(0b1010), f(0b101), f(0b0110), f(0b011)]),
            [f(0b1100 | (0b110 << 4))]
        );

        // rows that are not in the tables
        for row in [
            [f(1), f(2), f(3), f(3)], // carry is out of range
            [f(1), f(2), f(0), f(2)], // wrong output
        ] {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                xor_8_with_carry.lookup_row(&row)
            }));
            assert!(result.is_err());
        }
        // 3-bit input is out of range
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            xor_4x3.lookup_row(&[f(1), f(8), f(0), f(0), f(1)])
        }));
        assert!(result.is_err());
    }

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
