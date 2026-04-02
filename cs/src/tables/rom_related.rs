use super::*;

pub const ROM_PADDING_OPCODE: u32 = 0x0;

// pub fn create_rom_separator_table<
//     F: PrimeField,
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
// >(
//     id: u32,
// ) -> LookupTable<F> {
//     let keys = key_for_continuous_log2_range::<F, 1>(16);
//     const TABLE_NAME: &'static str = "ROM address space separator table";
//     LookupTable::create_table_from_key_and_pure_generation_fn(
//         &keys,
//         TABLE_NAME.to_string(),
//         1,
//         2,
//         |keys| {
//             let a = keys[0].as_u32_reduced();
//             assert!(a < (1u32 << 16));

//             let bound = 1 << ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
//             let input = a;
//             let is_rom = input < bound;
//             let rom_addr_high = input % bound;

//             let mut result = ArrayVec::new();
//             result.push(F::from_u32_unchecked(is_rom as u32));
//             result.push(F::from_u32_unchecked(rom_addr_high));

//             (a as usize, result)
//         },
//         Some(first_key_index_gen_fn::<F>),
//         id,
//     )
// }

/// Creating a table with ROM (program) data.
/// The table will have a constant size (ROM_ADDRESS_SPACE_BOUND / 4), and look like this:
/// (0, image bytes 0..2, image bytes 2..4)
/// (4, image bytes 4..6, image bytes 6..8)
// We have to do this his way, as our prime field is a little bit smaller than 32 bits.
// All the entries larger than the image will be filled with UNIMP_OPCODE.
pub fn create_table_for_rom_image<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    image: &[u32],
    id: u32,
) -> LookupTable<F> {
    assert!(ROM_ADDRESS_SPACE_SECOND_WORD_BITS > 0);

    assert!(
        image.len() * 4 <= 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        "ROM size can be at most {} bytes ({} words), but input is {} words",
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
        image.len()
    );

    let keys_len = 1usize << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2);
    let mut keys = Vec::with_capacity(keys_len);
    (0..keys_len)
        .into_par_iter()
        .map(|i| {
            let mut key = [F::ZERO];
            let address = i * 4;
            key[0] = F::from_u32_unchecked(address as u32);
            key
        })
        .collect_into_vec(&mut keys);

    assert_eq!(keys.len(), keys_len);
    const TABLE_NAME: &'static str = "ROM table";
    let image = image.to_vec();
    LookupTable::<F>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        2,
        move |key| {
            let pc = key[0].as_u32_reduced();
            assert!(
                pc < 1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
                "PC = {} is too large for ROM bound {} bytes",
                pc,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(pc % 4 == 0, "PC = {} is not aligned", pc);
            let index = (pc as usize) / 4;
            let opcode = if index < image.len() {
                image[index]
            } else {
                ROM_PADDING_OPCODE
            };
            let low = opcode as u16;
            let high = (opcode >> 16) as u16;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(low as u32));
            result.push(F::from_u32_unchecked(high as u32));

            ((pc / 4) as usize, result)
        },
        Some(|keys| {
            let pc = keys[0].as_u32_reduced();
            assert!(
                pc < 1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
                "PC = {} is too large for ROM bound {}",
                pc,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(pc % 4 == 0, "PC = {} is not aligned", pc);
            let index = (pc / 4) as usize;

            index
        }),
        id,
    )
}

pub fn create_load_halfword_from_rom_table<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    image: &[u32],
    id: u32,
) -> LookupTable<F> {
    assert!(ROM_ADDRESS_SPACE_SECOND_WORD_BITS > 0);

    assert!(
        image.len() * 4 <= 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        "ROM size can be at most {} bytes ({} words), but input is {} words",
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
        image.len()
    );

    let keys_len = 1usize << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS);
    let mut keys = Vec::with_capacity(keys_len);
    (0..keys_len)
        .into_par_iter()
        .map(|i| {
            let mut key = [F::ZERO];
            let word_address = (i >> 2) * 4;
            let signextend = (i >> 1) & 1;
            let use_high_half = i & 1;
            key[0] = F::from_u32_unchecked(
                (word_address
                    | (signextend << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS))
                    | (use_high_half << (17 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)))
                    as u32,
            );
            key
        })
        .collect_into_vec(&mut keys);

    assert_eq!(keys.len(), keys_len);
    const TABLE_NAME: &'static str = "ROM halfword read table";
    let image = image.to_vec();
    LookupTable::<F>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        2,
        move |key| {
            let input = key[0].as_u32_reduced();
            let address_mask = (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) - 1;
            let address = input & address_mask;
            let signextend = ((input >> (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) & 1) != 0;
            let use_high_half = ((input >> (17 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) & 1) != 0;

            assert!(
                address < (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)),
                "address = {} is too large for ROM bound {} bytes",
                address,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(address % 4 == 0, "address = {} is not aligned", address);

            let index = (address as usize) / 4;
            let opcode = if index < image.len() {
                image[index]
            } else {
                ROM_PADDING_OPCODE
            };
            let selected_halfword = if use_high_half {
                (opcode >> 16) as u16
            } else {
                opcode as u16
            };
            let sign_bit = signextend && ((selected_halfword >> 15) != 0);

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(selected_halfword as u32));
            result.push(F::from_u32_unchecked(if sign_bit { 0xffff } else { 0 }));

            (input as usize, result)
        },
        Some(|keys| {
            let input = keys[0].as_u32_reduced();
            let address_mask = (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) - 1;
            let address = input & address_mask;

            assert!(
                address < (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)),
                "address = {} is too large for ROM bound {} bytes",
                address,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(address % 4 == 0, "address = {} is not aligned", address);

            input as usize
        }),
        id,
    )
}

pub fn create_load_byte_from_rom_table<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    image: &[u32],
    id: u32,
) -> LookupTable<F> {
    assert!(ROM_ADDRESS_SPACE_SECOND_WORD_BITS > 0);

    assert!(
        image.len() * 4 <= 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        "ROM size can be at most {} bytes ({} words), but input is {} words",
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
        image.len()
    );

    let keys_len = 1usize << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS + 1);
    let mut keys = Vec::with_capacity(keys_len);
    (0..keys_len)
        .into_par_iter()
        .map(|i| {
            let mut key = [F::ZERO];
            let word_address = (i >> 3) * 4;
            let signextend = (i >> 2) & 1;
            let use_high_half = (i >> 1) & 1;
            let use_high_byte = i & 1;
            key[0] = F::from_u32_unchecked(
                (word_address
                    | (signextend << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS))
                    | (use_high_half << (17 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS))
                    | (use_high_byte << (18 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)))
                    as u32,
            );
            key
        })
        .collect_into_vec(&mut keys);

    assert_eq!(keys.len(), keys_len);
    const TABLE_NAME: &'static str = "ROM byte read table";
    let image = image.to_vec();
    LookupTable::<F>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        2,
        move |key| {
            let input = key[0].as_u32_reduced();
            let address_mask = (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) - 1;
            let address = input & address_mask;
            let signextend = ((input >> (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) & 1) != 0;
            let use_high_half = ((input >> (17 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) & 1) != 0;
            let use_high_byte = ((input >> (18 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) & 1) != 0;

            assert!(
                address < (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)),
                "address = {} is too large for ROM bound {} bytes",
                address,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(address % 4 == 0, "address = {} is not aligned", address);

            let index = (address as usize) / 4;
            let opcode = if index < image.len() {
                image[index]
            } else {
                ROM_PADDING_OPCODE
            };
            let selected_halfword = if use_high_half {
                (opcode >> 16) as u16
            } else {
                opcode as u16
            };
            let selected_byte = if use_high_byte {
                (selected_halfword >> 8) as u8
            } else {
                selected_halfword as u8
            };
            let sign_bit = signextend && ((selected_byte >> 7) != 0);

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(if sign_bit {
                (selected_byte as u32) | 0xff00
            } else {
                selected_byte as u32
            }));
            result.push(F::from_u32_unchecked(if sign_bit { 0xffff } else { 0 }));

            (input as usize, result)
        },
        Some(|keys| {
            let input = keys[0].as_u32_reduced();
            let address_mask = (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) - 1;
            let address = input & address_mask;

            assert!(
                address < (1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)),
                "address = {} is too large for ROM bound {} bytes",
                address,
                1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(address % 4 == 0, "address = {} is not aligned", address);

            input as usize
        }),
        id,
    )
}

// /// Creating a table with word-grained ROM (program) data.
// /// The table will have a constant size (ROM_ADDRESS_SPACE_BOUND / 4), and look like this:
// /// (0, image bytes 0..2, image bytes 2..4)
// /// (1, image bytes 4..6, image bytes 6..8)
// We have to do this his way, as our prime field is a little bit smaller than 32 bits.
// All the entries larger than the image will be filled with UNIMP_OPCODE.
// pub fn create_table_for_aligned_rom_image<
//     F: PrimeField,
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
// >(
//     image: &[u32],
//     id: u32,
// ) -> LookupTable<F, 3> {
//     use crate::tables::*;

//     assert!(ROM_ADDRESS_SPACE_SECOND_WORD_BITS > 0);

//     assert!(
//         image.len() * 4 <= 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
//         "ROM size can be at most {} bytes ({} words), but input is {} words",
//         1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
//         (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
//         image.len()
//     );

//     let keys = key_for_continuous_log2_range(16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2);

//     const TABLE_NAME: &'static str = "Word-grained ROM table";
//     let image = image.to_vec();
//     LookupTable::<F, 3>::create_table_from_key_and_key_generation_closure(
//         &keys,
//         TABLE_NAME.to_string(),
//         1,
//         move |key| {
//             let word_index = key[0].as_u64_reduced();
//             assert!(
//                 word_index < 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2) as u64,
//                 "Word index = {} is too large for ROM bound {} words",
//                 word_index,
//                 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2)
//             );
//             let word_index = word_index as usize;
//             let opcode = if word_index < image.len() {
//                 let opcode = image[word_index];

//                 opcode
//             } else {
//                 // UNIMP opcodes
//                 UNIMP_OPCODE
//             };
//             let low = opcode as u16;
//             let high = (opcode >> 16) as u16;

//             let mut result = [F::ZERO; 3];
//             result[0] = F::from_u64_unchecked(low as u64);
//             result[1] = F::from_u64_unchecked(high as u64);

//             (word_index as usize, result)
//         },
//         Some(first_key_index_gen_fn::<F, 3>),
//         id,
//     )
// }
