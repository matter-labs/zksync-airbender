use super::*;

pub fn create_conditional_op_resolution_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    // rs2 high || rs1 sign || rs1 < rs2 as unsigned || rs1 == rs2 || funct3

    const TABLE_WIDTH: usize = 16 + 1 + 1 + 1 + 3;
    const FUNCT3_MASK: u32 = 0b111u32;
    const RS2_MASK: u32 = u16::MAX as u32;
    const SRC1_SIGN_BIT_SHIFT: usize = 16;
    const UNSIGNED_LT_BIT_SHIFT: usize = 17;
    const EQ_BIT_SHIFT: usize = 18;
    const FUNCT3_BIT_SHIFT: usize = 19;

    let keys = key_for_continuous_log2_range::<F, 1>(TABLE_WIDTH);
    const TABLE_NAME: &'static str = "Conditional family resolution table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << TABLE_WIDTH));

            let input = a;
            let rs2 = input & RS2_MASK;
            let rs2_sign = rs2 >> 15 != 0;
            let rs1_sign = (input & (1 << SRC1_SIGN_BIT_SHIFT)) != 0;
            let funct3 = (input >> FUNCT3_BIT_SHIFT) & FUNCT3_MASK;
            let unsigned_lt_flag = (input & (1 << UNSIGNED_LT_BIT_SHIFT)) != 0;
            let eq_flag = (input & (1 << EQ_BIT_SHIFT)) != 0;

            // NOTE: Branch and SLT/SLTU tables are disjoint, so we output single table
            let resolved = match funct3 {
                0b000 => {
                    // BEQ
                    eq_flag
                }
                0b001 => {
                    // BNE
                    !eq_flag
                }
                0b010 | 0b100 => {
                    // SLT or BLT
                    if rs1_sign && !rs2_sign {
                        // rs1 < 0 and rs2 >= 0
                        true
                    } else if !rs1_sign && rs2_sign {
                        // rs1 >= 0 and rs2 < 0
                        false
                    } else {
                        // same sign, and then it matches unsigned comparison
                        unsigned_lt_flag
                    }
                }
                0b011 | 0b110 => {
                    // STLU or BLTU
                    unsigned_lt_flag
                }
                0b101 => {
                    // BGE — inverse of BLT
                    if rs1_sign && !rs2_sign {
                        false
                    } else if !rs1_sign && rs2_sign {
                        true
                    } else {
                        !unsigned_lt_flag
                    }
                }
                0b111 => {
                    // BGEU
                    // inverse of BLTU
                    !unsigned_lt_flag
                }

                _ => {
                    unreachable!()
                }
            };

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(resolved as u32));

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}

pub fn create_jump_cleanup_offset_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys = key_for_continuous_log2_range::<F, 1>(16);
    const TABLE_NAME: &'static str = "Jump offset check-cleanup table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        2,
        |keys| {
            let a = keys[0].as_u32_reduced();
            assert!(a < (1u32 << 16));

            let check_bit = (a >> 1) & 0x01;
            let output = a & (!0x3);

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(check_bit as u32));
            result.push(F::from_u32_unchecked(output as u32));

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

    /// Pack a key exactly as `create_conditional_op_resolution_table` decodes it:
    /// bits 0..16 = rs2 high half (rs2_sign = bit 15), bit 16 = rs1_sign,
    /// bit 17 = rs1<rs2 unsigned, bit 18 = rs1==rs2, bits 19..22 = funct3.
    fn packed_key(rs2_high: u32, rs1_sign: bool, unsigned_lt: bool, eq: bool, funct3: u32) -> u32 {
        (rs2_high & 0xFFFF)
            | ((rs1_sign as u32) << 16)
            | ((unsigned_lt as u32) << 17)
            | ((eq as u32) << 18)
            | (funct3 << 19)
    }

    #[test]
    fn conditional_jmp_branch_slt_cross_sign() {
        let table = create_conditional_op_resolution_table::<BabyBearField>(0);
        let resolve = |rs2_high, rs1_sign, unsigned_lt, eq, funct3| -> u32 {
            let k = packed_key(rs2_high, rs1_sign, unsigned_lt, eq, funct3);
            table.lookup_value::<1>(&[BabyBearField::new(k)])[0].as_u32_reduced()
        };

        // rs1 = 1 (sign 0), rs2 = -1 (high half 0xFFFF, sign 1), unsigned_lt = true.
        // Signed `1 < -1` = false.
        for funct3 in [0b010u32, 0b100] {
            assert_eq!(
                resolve(0xFFFF, false, true, false, funct3),
                0,
                "SLT/BLT(1,-1) must be signed-0 despite unsigned_lt=1 (funct3={funct3:#05b})"
            );
        }
        // rs1 = -1 (sign 1), rs2 = 1 (high half 0, sign 0), unsigned_lt = false.
        // Signed `-1 < 1` = true.
        for funct3 in [0b010u32, 0b100] {
            assert_eq!(
                resolve(0x0000, true, false, false, funct3),
                1,
                "SLT/BLT(-1,1) must be signed-1 despite unsigned_lt=0 (funct3={funct3:#05b})"
            );
        }
        // BGE is the inverse of BLT: BGE(1,-1) signed `1 >= -1` = true.
        assert_eq!(
            resolve(0xFFFF, false, true, false, 0b101),
            1,
            "BGE(1,-1) must be signed-1"
        );
    }
}
