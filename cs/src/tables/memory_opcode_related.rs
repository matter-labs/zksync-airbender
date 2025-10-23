use super::*;

pub fn create_memory_offset_lowest_bits_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Memory offset lowest bits table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            // output lowest two bits
            let lowest = a & 0x01;
            let second = (a >> 1) & 0x01;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(lowest as u64);
            result[1] = F::from_u64_unchecked(second as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_load_signs_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Get sign bits table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            // get bits 7 and 15
            let sign_if_u8 = (a >> 7) & 0x01;
            let sign_if_u16 = (a >> 15) & 0x01;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(sign_if_u8 as u64);
            result[1] = F::from_u64_unchecked(sign_if_u16 as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_mem_load_extend_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // 16-bit half-word || low/high value bit || funct3
    let keys = key_for_continuous_log2_range(16 + 1 + 3);

    let table_name = "Extend LOAD value table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < 1 << (16 + 1 + 3));

            let word = a as u16;
            let use_high_half = ((a >> 16) & 1) != 0;
            let funct3 = (a >> 17) as u8;

            let selected_byte = if use_high_half {
                (word >> 8) as u8
            } else {
                word as u8
            };

            #[allow(non_snake_case)]
            let loaded_word = match funct3 {
                _LB @ 0b000 => {
                    // sign-extend selected byte
                    let sign = (selected_byte >> 7) != 0;
                    if sign {
                        (selected_byte as u32) | 0xffffff00
                    } else {
                        selected_byte as u32
                    }
                }
                _LBU @ 0b100 => {
                    // zero-extend selected byte
                    selected_byte as u32
                }
                _LH @ 0b001 => {
                    // sign-extend selected word
                    let sign = (word >> 15) != 0;
                    if sign {
                        (word as u32) | 0xffff0000
                    } else {
                        word as u32
                    }
                }
                _LHU @ 0b101 => {
                    // zero-extend selected word
                    word as u32
                }
                _ => {
                    // Not important
                    0u32
                }
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked((loaded_word & 0xffff) as u64);
            result[1] = F::from_u64_unchecked((loaded_word >> 16) as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_store_byte_source_contribution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (16 + 1));
    for first in 0..(1 << 16) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Store byte source contribution table");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            let bit_0 = b != 0;
            let byte = a as u8;
            let result_half_word = if bit_0 {
                (byte as u16) << 8
            } else {
                byte as u16
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(result_half_word as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 16));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_store_byte_existing_contribution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (16 + 1));
    for first in 0..(1 << 16) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Store byte existing contribution table");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            // we need to cleanup a part of it to prepare for addition
            let bit_0 = b != 0;
            let result_half_word = if bit_0 {
                (a as u16) & 0x00ff
            } else {
                (a as u16) & 0xff00
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(result_half_word as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 16));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_memory_offset_mask_with_trap_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_MAX_WIDTH: usize = 16 + 3 + 1 + 1; // offset low || funct3 || is_store || rd_is_zero
    let keys = key_for_continuous_log2_range(TABLE_MAX_WIDTH);
    const TABLE_NAME: &'static str = "Memory offset and special bitmask with Trap table";
    const NUM_INPUTS: usize = 1;
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        NUM_INPUTS,
        |keys| {
            let input = keys[0].as_u64_reduced();
            assert!(input < (1 << TABLE_MAX_WIDTH));

            let mem_address_low = input & 0xffff;
            let funct3 = (input >> 16) & 0b111;
            let is_store = (input >> 17) & 0b1 != 0;
            let rd_is_x0 = (input >> 18) & 0b1 != 0;

            // offset is always 2 lowest bits of the address
            let offset = mem_address_low & 0b11;

            // now we need to resolve a trap, and decode for future ops if we
            // will use low or high word of RAM/ROM words for selections
            // and execution of less-than-word loads

            // NOTE that we must not trap if it's unaligned load,
            // but rd == 0

            // resolve base base - only based on funct3 and offset
            let mut less_than_word = false;
            let mut is_trap = match (funct3, offset) {
                (0b010, offset) => {
                    // LW or SW
                    offset != 0
                }
                (0b001, offset) | (0b101, offset) => {
                    // LH or LHU, or SH
                    less_than_word = true;
                    offset & 0b1 != 0
                }
                (0b000, _) | (0b100, _) => {
                    // LB or LBU, or SB
                    less_than_word = true;
                    false
                }
                _ => true,
            };
            let valid_funct3_for_load = match funct3 {
                0b000 | 0b100 | 0b001 | 0b101 | 0b010 => true,
                _ => false,
            };

            if valid_funct3_for_load && is_store == false && rd_is_x0 {
                is_trap = false;
            }

            // now resolve
            let use_high_limb = offset > 1; // 2 or 3

            let mut bitmask = less_than_word as u64;
            bitmask |= (use_high_limb as u64) << 1;
            bitmask |= (is_trap as u64) << 2;

            assert!(bitmask < 1u64 << crate::machine::ops::unrolled::load_store::MEMORY_GET_OFFSET_AND_MASK_NUM_BITS_WITH_TRAP);

            let result = [
                F::from_u64_unchecked(offset),
                F::from_u64_unchecked(bitmask),
                F::ZERO,
            ];
            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_load_halfword_or_byte_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_MAX_WIDTH: usize = 16 + 2 + 3; // limb (pre-selected whether low or high) || offset mod 4 || funct3
    let keys = key_for_continuous_log2_range(TABLE_MAX_WIDTH);
    const TABLE_NAME: &'static str = "Memory load (half-word and byte) output table";
    const NUM_INPUTS: usize = 1;
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        NUM_INPUTS,
        |keys| {
            let input = keys[0].as_u64_reduced();
            assert!(input < (1 << TABLE_MAX_WIDTH));

            let limb_value = input & 0xffff;
            let offset = (input >> 16) & 0b11;
            let funct3 = (input >> 18) & 0b111;
            let use_low_byte = offset & 1 == 0;

            let (low, high) = match (funct3, offset) {
                (0b010, _) => {
                    // LW or SW
                    // it's irrelevant - this table's output will only be used if we do less than word op
                    (0, 0)
                }
                (0b001, offset) => {
                    // LH, need sign extension
                    if offset & 1 != 0 {
                        // even though it's invalid offset, we do not care and provide some trivial value
                        (0, 0)
                    } else {
                        let sign_bit = (limb_value >> 15) != 0;
                        if sign_bit {
                            (limb_value, 0xffff)
                        } else {
                            (limb_value, 0)
                        }
                    }
                }
                (0b101, offset) => {
                    // LHU, no sign extension
                    if offset & 1 != 0 {
                        // even though it's invalid offset, we do not care and provide some trivial value
                        (0, 0)
                    } else {
                        (limb_value, 0)
                    }
                }
                (0b000, _) => {
                    // LB, need sign extension
                    let source = if use_low_byte {
                        limb_value & 0xff
                    } else {
                        limb_value >> 8
                    };
                    let sign_bit = (source >> 7) != 0;
                    if sign_bit {
                        (source | 0xff00, 0xffff)
                    } else {
                        (source, 0)
                    }
                }
                (0b100, _) => {
                    // LBU, no sign extension
                    let source = if use_low_byte {
                        limb_value & 0xff
                    } else {
                        limb_value >> 8
                    };
                    (source, 0)
                }
                _ => {
                    // also do not care about padding - any traps would happen before
                    (0, 0)
                }
            };

            let result = [
                F::from_u64_unchecked(low),
                F::from_u64_unchecked(high),
                F::ZERO,
            ];
            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_store_halfword_or_byte_clear_source_limb_table<F: PrimeField>(
    id: u32,
) -> LookupTable<F, 3> {
    const TABLE_MAX_WIDTH: usize = 16 + 2 + 3; // limb (pre-selected whether low or high) || offset mod 4 || funct3
    let keys = key_for_continuous_log2_range(TABLE_MAX_WIDTH);
    const TABLE_NAME: &'static str = "Memory store (half-word and byte) input limb cleanup table";
    const NUM_INPUTS: usize = 1;
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        NUM_INPUTS,
        |keys| {
            let input = keys[0].as_u64_reduced();
            assert!(input < (1 << TABLE_MAX_WIDTH));

            // we already pre-selected word to be consistent with top bit of the offset,
            // so unless we manipulate bytes then we do not care

            // We also do not use second output at all

            let limb_value = input & 0xffff;
            let offset = (input >> 16) & 0b11;
            let funct3 = (input >> 18) & 0b111;

            let cleaned_value = match (funct3, offset) {
                (0b010, _) => {
                    // SW
                    // it's irrelevant - this table's output will only be used if we do less than word op
                    0
                }
                (0b001, _) => {
                    // SH
                    // will be completely overwritten
                    0
                }
                (0b000, offset) => {
                    // SB, need to pick one half
                    let mask = if offset & 1 != 0 { 0x00ff } else { 0xff00 };

                    limb_value & mask
                }
                _ => {
                    // also do not care about padding - any traps would happen before
                    0
                }
            };

            let result = [F::from_u64_unchecked(cleaned_value), F::ZERO, F::ZERO];
            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_store_halfword_or_byte_clear_written_limb_table<F: PrimeField>(
    id: u32,
) -> LookupTable<F, 3> {
    const TABLE_MAX_WIDTH: usize = 16 + 2 + 3; // limb (pre-selected whether low or high) || offset mod 4 || funct3
    let keys = key_for_continuous_log2_range(TABLE_MAX_WIDTH);
    const TABLE_NAME: &'static str =
        "Memory store (half-word and byte) value to write limb cleanup table";
    const NUM_INPUTS: usize = 1;
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        NUM_INPUTS,
        |keys| {
            let input = keys[0].as_u64_reduced();
            assert!(input < (1 << TABLE_MAX_WIDTH));

            // we already pre-selected word to be consistent with top bit of the offset,
            // so unless we manipulate bytes then we do not care

            // We also do not use second output at all

            let limb_value = input & 0xffff;
            let offset = (input >> 16) & 0b11;
            let funct3 = (input >> 18) & 0b111;

            let cleaned_value = match (funct3, offset) {
                (0b010, _) => {
                    // SW
                    // it's irrelevant - this table's output will only be used if we do less than word op
                    0
                }
                (0b001, _) => {
                    // SH
                    // use the limb itself
                    limb_value
                }
                (0b000, offset) => {
                    // SB
                    let value_to_store = limb_value & 0xff;
                    // then we need to place it into high or low part
                    if offset & 1 != 0 {
                        value_to_store << 8
                    } else {
                        value_to_store
                    }
                }
                _ => {
                    // also do not care about padding - any traps would happen before
                    0
                }
            };

            let result = [F::from_u64_unchecked(cleaned_value), F::ZERO, F::ZERO];
            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
