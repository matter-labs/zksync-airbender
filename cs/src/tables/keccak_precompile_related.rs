use super::*;

pub const KECCAK_PERMUTATIONS_ADJUSTED: [u64; 25 * 25] = {
    let perms = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
        0, 9, 13, 17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11, 15, 12, 16, 20, 4, 8,
        0, 22, 19, 11, 8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18, 10, 7, 4, 13, 5, 2, 24, 16,
        0, 14, 23, 7, 16, 11, 20, 9, 18, 2, 22, 6, 15, 4, 13, 8, 17, 1, 10, 24, 19, 3, 12, 21, 5,
        0, 20, 15, 10, 5, 7, 2, 22, 17, 12, 14, 9, 4, 24, 19, 16, 11, 6, 1, 21, 23, 18, 13, 8, 3,
        0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18,
        0, 12, 24, 6, 18, 1, 13, 20, 7, 19, 2, 14, 21, 8, 15, 3, 10, 22, 9, 16, 4, 11, 23, 5, 17,
        0, 13, 21, 9, 17, 6, 19, 2, 10, 23, 12, 20, 8, 16, 4, 18, 1, 14, 22, 5, 24, 7, 15, 3, 11,
        0, 19, 8, 22, 11, 9, 23, 12, 1, 15, 13, 2, 16, 5, 24, 17, 6, 20, 14, 3, 21, 10, 4, 18, 7,
        0, 23, 16, 14, 7, 22, 15, 13, 6, 4, 19, 12, 5, 3, 21, 11, 9, 2, 20, 18, 8, 1, 24, 17, 10,
        0, 15, 5, 20, 10, 14, 4, 19, 9, 24, 23, 13, 3, 18, 8, 7, 22, 12, 2, 17, 16, 6, 21, 11, 1,
        0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6,
        0, 24, 18, 12, 6, 2, 21, 15, 14, 8, 4, 23, 17, 11, 5, 1, 20, 19, 13, 7, 3, 22, 16, 10, 9,
        0, 21, 17, 13, 9, 12, 8, 4, 20, 16, 24, 15, 11, 7, 3, 6, 2, 23, 19, 10, 18, 14, 5, 1, 22,
        0, 8, 11, 19, 22, 13, 16, 24, 2, 5, 21, 4, 7, 10, 18, 9, 12, 15, 23, 1, 17, 20, 3, 6, 14,
        0, 16, 7, 23, 14, 19, 5, 21, 12, 3, 8, 24, 10, 1, 17, 22, 13, 4, 15, 6, 11, 2, 18, 9, 20,
        0, 5, 10, 15, 20, 23, 3, 8, 13, 18, 16, 21, 1, 6, 11, 14, 19, 24, 4, 9, 7, 12, 17, 22, 2,
        0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12,
        0, 18, 6, 24, 12, 4, 17, 5, 23, 11, 3, 16, 9, 22, 10, 2, 15, 8, 21, 14, 1, 19, 7, 20, 13,
        0, 17, 9, 21, 13, 24, 11, 3, 15, 7, 18, 5, 22, 14, 1, 12, 4, 16, 8, 20, 6, 23, 10, 2, 19,
        0, 11, 22, 8, 19, 21, 7, 18, 4, 10, 17, 3, 14, 20, 6, 13, 24, 5, 16, 2, 9, 15, 1, 12, 23,
        0, 7, 14, 16, 23, 8, 10, 17, 24, 1, 11, 18, 20, 2, 9, 19, 21, 3, 5, 12, 22, 4, 6, 13, 15,
        0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4,
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    ];
    let mut i = 0;
    while i < perms.len() {
        assert!(perms[i] < 25);
        i += 1;
    }
    perms
};

// WARNING: IF THE CONTROL IS TOTALLY EMPTY THIS WILL OUTPUT JUNK
pub fn create_keccak_permutation_indices_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
    const PRECOMPILE_COLUMNMIX1: u32 = 1;
    const PRECOMPILE_COLUMNMIX2: u32 = 2;
    const PRECOMPILE_THETA: u32 = 3;
    const PRECOMPILE_RHO: u32 = 4;
    const PRECOMPILE_CHI1: u32 = 5;
    const PRECOMPILE_CHI2: u32 = 6;

    const PERMUTATIONS_ADJUSTED: [u64; 25 * 25] = KECCAK_PERMUTATIONS_ADJUSTED;
    let mut keys = Vec::with_capacity(1 << 12);
    for control_with_exe in 0..1 << 12 {
        let key = [F::from_u32_unchecked(control_with_exe)];
        keys.push(key);
    }
    let table_name = format!("keccak permutation indices table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        6,
        |keys| {
            let control_with_exe = keys[0].as_u32_reduced();
            debug_assert!(control_with_exe < (1 << 12));

            let control = control_with_exe & 0b0111_1111_1111;
            let exe = (control_with_exe >> 11) == 1;
            let precompile = control as u32 & 0b111;
            let iter = (control as usize >> 3) & 0b111;
            let round = control as usize >> 6;

            // debug_assert!(precompile < 5 && (control & (1<<precompile))!=0, "NOT {control:0b} -> p{precompile}");
            // debug_assert!(iter < 5 && ((control >> 5) & (1<<iter))!=0);
            let indices = match precompile {
                PRECOMPILE_IOTA_COLUMNXOR if iter < 5 && round <= 24 && exe => {
                    let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25]; // indices before applying round permutation
                    let idcol = 25 + iter as u64;
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, idcol]
                }
                PRECOMPILE_COLUMNMIX1 if iter < 5 && round < 24 => [25, 26, 27, 28, 29, 30],
                PRECOMPILE_COLUMNMIX2 if iter < 5 && round < 24 => [25, 26, 27, 28, 29, 30],
                PRECOMPILE_THETA if iter < 5 && round < 24 => {
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
                PRECOMPILE_RHO if iter < 5 && round < 24 => {
                    let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25]; // indices before applying round permutation
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, 25]
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
                0 if iter == 0 && round == 0 => {
                    assert_eq!(control, 0);
                    [0, 0, 0, 0, 0, 0]
                }
                _ => [0, 1, 2, 3, 4, 5], // THIS IS JUNK!!!!
            };

            let mut result = ArrayVec::new();
            result
                .try_extend_from_slice(&indices.map(|el| F::from_u32_with_reduction(el as u32)))
                .unwrap();

            (control as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}

// WARN: if you call this with a wrong round it returns junk!
pub fn create_xor_special_keccak_iota_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    const ROUND_CONSTANTS_ADJUSTED: [u64; 25] = [
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
        0x8000000080008008, // last round, adjusted to fictitious 25th round
    ];
    let mut keys = Vec::with_capacity(1 << 16);
    for b in 0..1 << 8 {
        for a in 0..1 << 8 {
            let key = [F::from_u32_unchecked(a), F::from_u32_unchecked(b)];
            keys.push(key);
        }
    }
    let table_name = format!("Keccak Special Xor with Iota Round Constants table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b_control = keys[1].as_u32_reduced();
            debug_assert!(a < (1 << 8) && b_control < (1 << 8));

            let round_if_iter0 = (b_control & 0b11111) as usize;
            let u8_position = (b_control >> 5) as usize;

            let b = if round_if_iter0 <= 24 {
                let round_constant = ROUND_CONSTANTS_ADJUSTED[round_if_iter0];
                let u8_chunks = round_constant.to_le_bytes();
                u8_chunks[u8_position] as u64
            } else {
                0
            }; // THIS IS JUNK
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(a ^ (b as u32)));

            ((a | b_control << 8) as usize, result)
        },
        Some(|keys| (keys[0].as_u32_reduced() | keys[1].as_u32_reduced() << 8) as usize),
        id,
    )
}

pub fn create_andn_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let mut keys = Vec::with_capacity(1 << 16);
    for b in 0..1 << 8 {
        for a in 0..1 << 8 {
            let key = [F::from_u32_unchecked(a), F::from_u32_unchecked(b)];
            keys.push(key);
        }
    }
    let table_name = format!("AndNot (ie. !a & b) table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        1,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            debug_assert!(a < (1 << 8) && b < (1 << 8));

            let c = !a & b;

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(c));

            ((a | b << 8) as usize, result)
        },
        Some(|keys| (keys[0].as_u32_reduced() | keys[1].as_u32_reduced() << 8) as usize),
        id,
    )
}
pub fn create_rotl_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let mut keys = Vec::with_capacity(1 << 20);
    for rot_const in 0..16 {
        for word_u16 in 0..1 << 16 {
            let key = [F::from_u32_unchecked(word_u16 | rot_const << 16)];
            keys.push(key);
        }
    }
    let table_name = format!("RotateLeft u16 table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        2,
        |keys| {
            let input = keys[0].as_u32_reduced();
            debug_assert!(input < (1 << 20));

            let word_u16 = input as u16;
            let rot_const = (input >> 16) as u32;

            let (left, right) = (
                word_u16.unbounded_shr(16 - rot_const),
                word_u16.unbounded_shl(rot_const),
            );

            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(left as u32));
            result.push(F::from_u32_unchecked(right as u32));

            (input as usize, result)
        },
        Some(|keys| keys[0].as_u32_reduced() as usize),
        id,
    )
}

// Keccak-f1600 control word: precompile | iteration << 3 | round << 6; table keys add the execute flag at bit 11
use common_constants::delegation_types::keccak_f1600::{
    KECCAK_CHI5_PRECOMPILE, KECCAK_THETA_RHO_PRECOMPILE,
};

const fn keccak_control(precompile: u32, iteration: u32, round: u32) -> u32 {
    precompile | iteration << 3 | round << 6
}

// key 0 is padding; column parity also runs in round 24 (iteration 0) for the delayed iota
fn keccak_control_row(key: u32, precompile: u32) -> Option<(usize, u32, u32)> {
    if key == 0 {
        return None;
    }
    let control = key & 0x7ff;
    assert_eq!(key >> 11, 1, "control key without execute flag");
    assert_eq!(control & 0b111, precompile);
    let iteration = (control >> 3) & 0b111;
    let round = control >> 6;
    assert!(iteration < 5 && (round < 24 || (round == 24 && iteration == 0 && precompile == 0)));
    Some((1 + (round * 5 + iteration) as usize, iteration, round))
}

fn keccak_control_keys<F: PrimeField>(precompile: u32) -> Vec<[F; 1]> {
    let mut keys = vec![[F::ZERO]];
    for round in 0..24 {
        for iteration in 0..5 {
            let control = keccak_control(precompile, iteration, round);
            keys.push([F::from_u32_unchecked(control | 1 << 11)]);
        }
    }
    if precompile == 0 {
        keys.push([F::from_u32_unchecked(keccak_control(0, 0, 24) | 1 << 11)]);
    }
    keys
}

fn keccak_theta_rho_row(key: u32) -> Option<(usize, u32, u32)> {
    keccak_control_row(key, KECCAK_THETA_RHO_PRECOMPILE)
}

fn keccak_theta_rho_keys<F: PrimeField>() -> Vec<[F; 1]> {
    keccak_control_keys(KECCAK_THETA_RHO_PRECOMPILE)
}

fn padded_row<F: PrimeField, const N: usize>(
    row: Option<(usize, [u32; N])>,
) -> (usize, ArrayVec<F, 16>) {
    let (index, values) = row.unwrap_or((0, [0; N]));
    (
        index,
        values.into_iter().map(F::from_u32_unchecked).collect(),
    )
}

pub fn create_keccak_theta_rho_d_indices_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_theta_rho_keys::<F>(),
        "keccak theta/rho with in-row D indices".to_string(),
        1,
        7,
        |keys| {
            padded_row(
                keccak_theta_rho_row(keys[0].as_u32_reduced()).map(|(index, x, round)| {
                    let pi = &KECCAK_PERMUTATIONS_ADJUSTED[round as usize * 25..][..25];
                    let values: [u32; 7] = core::array::from_fn(|i| match i {
                        0..5 => pi[x as usize + 5 * i] as u32,
                        5 => 25 + (x + 4) % 5,
                        _ => 25 + (x + 1) % 5,
                    });
                    (index, values)
                }),
            )
        },
        None,
        id,
    )
}

// (p, c, o) -> ((c << 1) & 15 | p >> 3) ^ o: nibble k of rotl(C, 1) ^ other, from nibbles k - 1 and
// k of C
pub fn create_keccak_rot1_xor_nibble_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys: Vec<[F; 3]> = (0..1u32 << 12)
        .map(|i| [i & 15, (i >> 4) & 15, i >> 8].map(F::from_u32_unchecked))
        .collect();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "keccak rotl1 xor nibble".to_string(),
        3,
        1,
        |keys| {
            let [p, c, o] = [0, 1, 2].map(|i| keys[i].as_u32_reduced());
            debug_assert!(p < 16 && c < 16 && o < 16);
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked((((c << 1) & 15) | (p >> 3)) ^ o));
            ((p | c << 4 | o << 8) as usize, result)
        },
        None,
        id,
    )
}

pub fn create_keccak_column_parity_indices_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F>(0),
        "keccak column parity indices".to_string(),
        1,
        6,
        |keys| {
            padded_row(
                keccak_control_row(keys[0].as_u32_reduced(), 0).map(|(index, x, round)| {
                    let pi = &KECCAK_PERMUTATIONS_ADJUSTED[round as usize * 25..][..25];
                    let values: [u32; 6] = core::array::from_fn(|i| match i {
                        0..5 => pi[x as usize + 5 * i] as u32,
                        _ => 25 + x,
                    });
                    (index, values)
                }),
            )
        },
        None,
        id,
    )
}

// next control and the round whose delayed iota constant applies (0 = none) in iteration 0
pub fn create_keccak_column_parity_control_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F>(0),
        "keccak column parity control".to_string(),
        1,
        2,
        |keys| {
            padded_row(
                keccak_control_row(keys[0].as_u32_reduced(), 0).map(|(index, x, round)| {
                    let next = if x < 4 {
                        keccak_control(0, x + 1, round)
                    } else {
                        keccak_control(KECCAK_THETA_RHO_PRECOMPILE, 0, round)
                    };
                    (index, [next, if x == 0 { round } else { 0 }])
                }),
            )
        },
        None,
        id,
    )
}

pub fn create_keccak_xor5_nibble_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys: Vec<[F; 5]> = (0..1u32 << 20)
        .map(|i| core::array::from_fn(|k| F::from_u32_unchecked((i >> (4 * k)) & 15)))
        .collect();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "keccak xor5 nibble".to_string(),
        5,
        1,
        |keys| {
            let nibbles: [u32; 5] = core::array::from_fn(|k| keys[k].as_u32_reduced());
            debug_assert!(nibbles.iter().all(|&n| n < 16));
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked(
                nibbles.iter().fold(0, |acc, n| acc ^ n),
            ));
            let index = nibbles.iter().rev().fold(0, |acc, &n| acc << 4 | n);
            (index as usize, result)
        },
        None,
        id,
    )
}

pub fn create_keccak_theta_rho_control_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_theta_rho_keys::<F>(),
        "keccak theta/rho control".to_string(),
        1,
        6,
        |keys| {
            let mut result = ArrayVec::new();
            let Some((index, iteration, round)) = keccak_theta_rho_row(keys[0].as_u32_reduced())
            else {
                for _ in 0..6 {
                    result.push(F::ZERO);
                }
                return (0, result);
            };
            let next = if iteration < 4 {
                keccak_control(KECCAK_THETA_RHO_PRECOMPILE, iteration + 1, round)
            } else {
                keccak_control(KECCAK_CHI5_PRECOMPILE, 0, round)
            };
            result.push(F::from_u32_unchecked(next));
            for x in 0..5 {
                result.push(F::from_u32_unchecked((x == iteration) as u32));
            }
            (index, result)
        },
        None,
        id,
    )
}

// (a, b, s) -> (((a ^ b) << s) & 0xff, (a ^ b) >> (8 - s)): the two fragments of a byte of
// rotl(a ^ b, 8q + s) that land in output bytes q and q + 1
pub fn create_keccak_xor_split_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let mut keys = Vec::with_capacity(1 << 19);
    for s in 0..8u32 {
        for b in 0..256u32 {
            for a in 0..256u32 {
                keys.push([
                    F::from_u32_unchecked(a),
                    F::from_u32_unchecked(b),
                    F::from_u32_unchecked(s),
                ]);
            }
        }
    }
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "keccak xor split".to_string(),
        3,
        2,
        |keys| {
            let a = keys[0].as_u32_reduced();
            let b = keys[1].as_u32_reduced();
            let s = keys[2].as_u32_reduced();
            debug_assert!(a < 256 && b < 256 && s < 8);
            let v = a ^ b;
            let mut result = ArrayVec::new();
            result.push(F::from_u32_unchecked((v << s) & 0xff));
            result.push(F::from_u32_unchecked(v.unbounded_shr(8 - s)));
            ((a | b << 8 | s << 16) as usize, result)
        },
        None,
        id,
    )
}
