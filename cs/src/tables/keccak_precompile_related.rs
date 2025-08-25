use super::*;

// WARNING: IF THE CONTROL IS TOTALLY EMPTY THIS WILL OUTPUT JUNK
pub fn create_keccak_permutation_indices_table<F: PrimeField, const I: usize, const J: usize>(
    id: u32,
) -> LookupTable<F, 3> {
    const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
    const PRECOMPILE_COLUMNMIX: u32 = 1;
    const PRECOMPILE_THETA_RHO: u32 = 2;
    const PRECOMPILE_CHI1: u32 = 3;
    const PRECOMPILE_CHI2: u32 = 4;
    const PERMUTATIONS_ADJUSTED: [u64; 25 * 25] = {
        let perms = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14,
            15, 21, 0, 9, 13, 17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11, 15, 12, 16,
            20, 4, 8, 0, 22, 19, 11, 8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18, 10, 7, 4, 13,
            5, 2, 24, 16, 0, 14, 23, 7, 16, 11, 20, 9, 18, 2, 22, 6, 15, 4, 13, 8, 17, 1, 10, 24,
            19, 3, 12, 21, 5, 0, 20, 15, 10, 5, 7, 2, 22, 17, 12, 14, 9, 4, 24, 19, 16, 11, 6, 1,
            21, 23, 18, 13, 8, 3, 0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9,
            6, 8, 15, 17, 19, 16, 18, 0, 12, 24, 6, 18, 1, 13, 20, 7, 19, 2, 14, 21, 8, 15, 3, 10,
            22, 9, 16, 4, 11, 23, 5, 17, 0, 13, 21, 9, 17, 6, 19, 2, 10, 23, 12, 20, 8, 16, 4, 18,
            1, 14, 22, 5, 24, 7, 15, 3, 11, 0, 19, 8, 22, 11, 9, 23, 12, 1, 15, 13, 2, 16, 5, 24,
            17, 6, 20, 14, 3, 21, 10, 4, 18, 7, 0, 23, 16, 14, 7, 22, 15, 13, 6, 4, 19, 12, 5, 3,
            21, 11, 9, 2, 20, 18, 8, 1, 24, 17, 10, 0, 15, 5, 20, 10, 14, 4, 19, 9, 24, 23, 13, 3,
            18, 8, 7, 22, 12, 2, 17, 16, 6, 21, 11, 1, 0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19,
            18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 0, 24, 18, 12, 6, 2, 21, 15, 14, 8, 4,
            23, 17, 11, 5, 1, 20, 19, 13, 7, 3, 22, 16, 10, 9, 0, 21, 17, 13, 9, 12, 8, 4, 20, 16,
            24, 15, 11, 7, 3, 6, 2, 23, 19, 10, 18, 14, 5, 1, 22, 0, 8, 11, 19, 22, 13, 16, 24, 2,
            5, 21, 4, 7, 10, 18, 9, 12, 15, 23, 1, 17, 20, 3, 6, 14, 0, 16, 7, 23, 14, 19, 5, 21,
            12, 3, 8, 24, 10, 1, 17, 22, 13, 4, 15, 6, 11, 2, 18, 9, 20, 0, 5, 10, 15, 20, 23, 3,
            8, 13, 18, 16, 21, 1, 6, 11, 14, 19, 24, 4, 9, 7, 12, 17, 22, 2, 0, 3, 1, 4, 2, 15, 18,
            16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 0, 18, 6, 24, 12, 4,
            17, 5, 23, 11, 3, 16, 9, 22, 10, 2, 15, 8, 21, 14, 1, 19, 7, 20, 13, 0, 17, 9, 21, 13,
            24, 11, 3, 15, 7, 18, 5, 22, 14, 1, 12, 4, 16, 8, 20, 6, 23, 10, 2, 19, 0, 11, 22, 8,
            19, 21, 7, 18, 4, 10, 17, 3, 14, 20, 6, 13, 24, 5, 16, 2, 9, 15, 1, 12, 23, 0, 7, 14,
            16, 23, 8, 10, 17, 24, 1, 11, 18, 20, 2, 9, 19, 21, 3, 5, 12, 22, 4, 6, 13, 15, 0, 10,
            20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4, 0,
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        ];
        let mut i = 0;
        while i < perms.len() {
            assert!(perms[i] < 30);
            i += 1;
        }
        perms
    };
    let mut keys = Vec::with_capacity(1 << 15);
    for control in 0..1 << 15 {
        let key = [F::from_u64_unchecked(control), F::ZERO, F::ZERO];
        keys.push(key);
    }
    let table_name = format!("Keccak Permutation Indices({I}, {J}) table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let control = keys[0].as_u64_reduced();
            debug_assert!(control < (1 << 15));

            let precompile = {
                let precompile_bitmask = control & 0b11111;
                precompile_bitmask.trailing_zeros()
            };
            let iter = {
                let iter_bitmask = (control >> 5) & 0b11111;
                iter_bitmask.trailing_zeros() as usize
            };
            let round = (control >> 10) as usize;

            // debug_assert!(precompile < 5 && (control & (1<<precompile))!=0, "NOT {control:0b} -> p{precompile}");
            // debug_assert!(iter < 5 && ((control >> 5) & (1<<iter))!=0);
            let indices = match precompile {
                PRECOMPILE_IOTA_COLUMNXOR if iter < 5 && round < 24 => {
                    let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25]; // indices before applying round permutation
                    let idcol = 25 + iter as u64;
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, idcol]
                }
                PRECOMPILE_COLUMNMIX if iter < 5 && round < 24 => [25, 26, 27, 28, 29, 0],
                PRECOMPILE_THETA_RHO if iter < 5 && round < 24 => {
                    const IDCOLS: [u64; 5] = [29, 25, 26, 27, 28];
                    let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25]; // indices before applying round permutation
                    let idcol = IDCOLS[iter];
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, idcol]
                }
                PRECOMPILE_CHI1 if iter < 5 && round < 24 => {
                    let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..][..25]; // indices after applying round permutation
                    let idx = iter * 5;
                    let _idx0 = pi[idx];
                    let idx1 = pi[idx + 1];
                    let idx2 = pi[idx + 2];
                    let idx3 = pi[idx + 3];
                    let idx4 = pi[idx + 4];
                    [idx1, idx2, idx3, idx4, 25, 26]
                }
                PRECOMPILE_CHI2 if iter < 5 && round < 24 => {
                    let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..][..25]; // indices after applying round permutation
                    let idx = iter * 5;
                    let idx0 = pi[idx];
                    let _idx1 = pi[idx + 1];
                    let _idx2 = pi[idx + 2];
                    let idx3 = pi[idx + 3];
                    let idx4 = pi[idx + 4];
                    [idx0, idx3, idx4, 25, 26, 27]
                }
                // explicit case of padding - when control == 0
                64 if iter == 64 && round == 0 => {
                    assert_eq!(control, 0);
                    [0, 0, 0, 0, 0, 0]
                }
                _ => [0, 1, 2, 3, 4, 5], // THIS IS JUNK!!!!
            };
            let result = [
                F::from_u64_unchecked(indices[I]),
                F::from_u64_unchecked(indices[J]),
                F::ZERO,
            ];
            (control as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

// WARN: if you call this with a wrong round it returns junk!
pub fn create_xor_special_keccak_iota_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const ROUND_CONSTANTS_ADJUSTED: [u64; 24] = [
        0,
        1,
        32898,
        9223372036854808714,
        9223372039002292224,
        32907,
        2147483649,
        9223372039002292353,
        9223372036854808585,
        138,
        136,
        2147516425,
        2147483658,
        2147516555,
        9223372036854775947,
        9223372036854808713,
        9223372036854808579,
        9223372036854808578,
        9223372036854775936,
        32778,
        9223372039002259466,
        9223372039002292353,
        9223372036854808704,
        2147483649,
    ];
    let mut keys = Vec::with_capacity(1 << 16);
    for b in 0..1 << 8 {
        for a in 0..1 << 8 {
            let key = [F::from_u64_unchecked(a), F::from_u64_unchecked(b), F::ZERO];
            keys.push(key);
        }
    }
    let table_name = format!("Keccak Special Xor with Iota Round Constants table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b_control = keys[1].as_u64_reduced();
            debug_assert!(a < (1 << 8) && b_control < (1 << 8));

            let round_if_iter0 = (b_control & 0b11111) as usize;
            let u8_position = (b_control >> 5) as usize;

            let b = if round_if_iter0 < 24 {
                let round_constant = ROUND_CONSTANTS_ADJUSTED[round_if_iter0];
                let u8_chunks = round_constant.to_le_bytes();
                u8_chunks[u8_position] as u64
            } else {
                0
            }; // THIS IS JUNK
            let result = [F::from_u64_unchecked(a ^ b), F::ZERO, F::ZERO];
            ((a | b_control << 8) as usize, result)
        },
        Some(|keys| (keys[0].as_u64_reduced() | keys[1].as_u64_reduced() << 8) as usize),
        id,
    )
}

pub fn create_andn_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << 16);
    for b in 0..1 << 8 {
        for a in 0..1 << 8 {
            let key = [F::from_u64_unchecked(a), F::from_u64_unchecked(b), F::ZERO];
            keys.push(key);
        }
    }
    let table_name = format!("AndNot (ie. !a & b) table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            debug_assert!(a < (1 << 8) && b < (1 << 8));

            let c = !a & b;
            let result = [F::from_u64_unchecked(c), F::ZERO, F::ZERO];
            ((a | b << 8) as usize, result)
        },
        Some(|keys| (keys[0].as_u64_reduced() | keys[1].as_u64_reduced() << 8) as usize),
        id,
    )
}
pub fn create_rotl_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << 20);
    for rot_const in 0..16 {
        for word_u16 in 0..1 << 16 {
            let key = [
                F::from_u64_unchecked(word_u16 | rot_const << 16),
                F::ZERO,
                F::ZERO,
            ];
            keys.push(key);
        }
    }
    let table_name = format!("RotateLeft u16 table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let input = keys[0].as_u64_reduced();
            debug_assert!(input < (1 << 20));

            let word_u16 = input as u16;
            let rot_const = (input >> 16) as u32;

            let (left, right) = (
                word_u16.unbounded_shr(16 - rot_const),
                word_u16.unbounded_shl(rot_const),
            );
            let result = [
                F::from_u64_unchecked(left as u64),
                F::from_u64_unchecked(right as u64),
                F::ZERO,
            ];
            (input as usize, result)
        },
        Some(|keys| keys[0].as_u64_reduced() as usize),
        id,
    )
}
