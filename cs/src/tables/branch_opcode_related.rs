use super::*;

pub fn create_conditional_op_resolution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 3 + 1 + 1 + 1 + 1;
    const FUNCT3_MASK: u64 = 0x7u64;
    const UNSIGNED_LT_BIT_SHIFT: usize = 3;
    const EQ_BIT_SHIFT: usize = 4;
    const SRC1_BIT_SHIFT: usize = 5;
    const SRC2_BIT_SHIFT: usize = 6;

    let keys = key_for_continuous_log2_range(TABLE_WIDTH);
    const TABLE_NAME: &'static str = "Conditional family resolution table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << TABLE_WIDTH));

            let input = a;
            let funct3 = input & FUNCT3_MASK;
            let unsigned_lt_flag = (input & (1 << UNSIGNED_LT_BIT_SHIFT)) != 0;
            let eq_flag = (input & (1 << EQ_BIT_SHIFT)) != 0;
            let src1_bit = (input & (1 << SRC1_BIT_SHIFT)) != 0;
            let src2_bit = (input & (1 << SRC2_BIT_SHIFT)) != 0;
            let operands_different_signs_flag = src1_bit ^ src2_bit;

            let (should_branch, should_store) = match funct3 {
                0b000 => {
                    // BEQ
                    if eq_flag {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b001 => {
                    // BNE
                    if eq_flag == false {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b010 => {
                    // STL
                    if operands_different_signs_flag {
                        // signs are different,
                        // so if rs1 is negative, and rs2 is positive (so condition holds)
                        // then LT must be be false
                        if unsigned_lt_flag == false {
                            (false, true)
                        } else {
                            (false, false)
                        }
                    } else {
                        // just unsigned comparison works for both cases
                        if unsigned_lt_flag {
                            (false, true)
                        } else {
                            (false, false)
                        }
                    }
                }
                0b011 => {
                    // STLU
                    // just unsigned comparison works for both cases
                    if unsigned_lt_flag {
                        (false, true)
                    } else {
                        (false, false)
                    }
                }
                0b100 => {
                    // BLT
                    if operands_different_signs_flag {
                        // signs are different,
                        // so if rs1 is negative, and rs2 is positive (so condition holds)
                        // then LT must be be false
                        if unsigned_lt_flag == false {
                            (true, false)
                        } else {
                            (false, false)
                        }
                    } else {
                        // just unsigned comparison works for both cases
                        if unsigned_lt_flag {
                            (true, false)
                        } else {
                            (false, false)
                        }
                    }
                }
                0b101 => {
                    // BGE
                    // inverse of BLT
                    if operands_different_signs_flag {
                        if unsigned_lt_flag == false {
                            (false, false)
                        } else {
                            (true, false)
                        }
                    } else {
                        if unsigned_lt_flag {
                            (false, false)
                        } else {
                            (true, false)
                        }
                    }
                }
                0b110 => {
                    // BLTU
                    if unsigned_lt_flag {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b111 => {
                    // BGEU
                    // inverse of BLTU
                    if unsigned_lt_flag {
                        (false, false)
                    } else {
                        (true, false)
                    }
                }

                _ => {
                    unreachable!()
                }
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(should_branch as u64);
            result[1] = F::from_u64_unchecked(should_store as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_conditional_jmp_branch_slt_family_resolution_table<F: PrimeField>(
    id: u32,
) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 3 + 1 + 1 + 1 + 1;

    let mut keys = Vec::with_capacity(1 << TABLE_WIDTH);
    for a in 0..1 << 4 {
        for b in 0..1 << 3 {
            let key = [F::from_u64_unchecked(a), F::from_u64_unchecked(b), F::ZERO];
            keys.push(key);
        }
    }
    assert!(keys.len() == 1 << TABLE_WIDTH);

    const TABLE_NAME: &'static str = "Conditional JUMP/BRANCH/SLT family resolution table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(a < (1 << 4)); // input bits
            assert!(b < (1 << 3)); // funct3

            let uf = a & 1; // uf flag for unsigned comparison op1 - op2
            let out_is_zero = (a >> 1) & 1; // op1 - op2 == 0
            let sign1 = (a >> 2) & 1; // sign of op1
            let sign2 = (a >> 3) & 1; // sign of op2
            let f3 = b;

            let eq = out_is_zero != 0;
            let unsigned_lt = uf != 0;
            let signed_lt = if sign1 ^ sign2 == 1 {
                sign1 != 0
            } else {
                unsigned_lt
            };

            // NOTE: not all funct3 are possible (e.g. in case of SLT),
            // but we do not care as decoder would filter those earlier

            #[expect(non_snake_case)]
            let flag = match f3 {
                _BEQ @ 0b000 => eq,
                _BNE @ 0b001 => !eq,
                _SLT_SLTI @ 0b010 => signed_lt,
                _SLTU_SLTIU @ 0b011 => unsigned_lt,
                _BLT @ 0b100 => signed_lt,
                _BGE @ 0b101 => !signed_lt,
                _BLTU @ 0b110 => unsigned_lt,
                _BGEU @ 0b111 => !unsigned_lt,
                _ => unreachable!(),
            };

            let result = [F::from_boolean(flag), F::ZERO, F::ZERO];
            (index_for_binary_key_for_width::<3>(a, b), result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(a < (1 << 4));
            assert!(b < (1 << 3));
            index_for_binary_key_for_width::<3>(a, b)
        }),
        id,
    )
}
