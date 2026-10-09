use super::*;
use common_constants::delegation_types::keccak_f1600::*;
use core::array::from_fn;

// WARNING: IF THE CONTROL IS TOTALLY EMPTY THIS WILL OUTPUT JUNK
pub fn create_keccak_permutation_indices_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
    const PRECOMPILE_COLUMNMIX1: u32 = 1;
    const PRECOMPILE_COLUMNMIX2: u32 = 2;
    const PRECOMPILE_THETA: u32 = 3;
    const PRECOMPILE_RHO: u32 = 4;
    const PRECOMPILE_CHI1: u32 = 5;
    const PRECOMPILE_CHI2: u32 = 6;

    let mut keys = Vec::with_capacity(1 << 12);
    for control_with_exe in 0..1 << 12 {
        let key = [F::from_u32_unchecked(control_with_exe)];
        keys.push(key);
    }
    let table_name = "keccak permutation indices table".to_string();

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
            let precompile = control & 0b111;
            let iter = (control as usize >> 3) & 0b111;
            let round = control as usize >> 6;

            // debug_assert!(precompile < 5 && (control & (1<<precompile))!=0, "NOT {control:0b} -> p{precompile}");
            // debug_assert!(iter < 5 && ((control >> 5) & (1<<iter))!=0);
            let indices = match precompile {
                PRECOMPILE_IOTA_COLUMNXOR if iter < 5 && round <= 24 && exe => {
                    let pi = &KECCAK_F1600_PERMUTATIONS[round]; // indices before applying round permutation
                    let idcol = 25 + iter;
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
                    const IDCOLS: [usize; 5] = [29, 25, 26, 27, 28];
                    let pi = &KECCAK_F1600_PERMUTATIONS[round]; // indices before applying round permutation
                    let idcol = IDCOLS[iter];
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, idcol]
                }
                PRECOMPILE_RHO if iter < 5 && round < 24 => {
                    let pi = &KECCAK_F1600_PERMUTATIONS[round]; // indices before applying round permutation
                    let idx0 = pi[iter];
                    let idx5 = pi[iter + 5];
                    let idx10 = pi[iter + 10];
                    let idx15 = pi[iter + 15];
                    let idx20 = pi[iter + 20];
                    [idx0, idx5, idx10, idx15, idx20, 25]
                }
                PRECOMPILE_CHI1 if iter < 5 && round < 24 => {
                    let pi = &KECCAK_F1600_PERMUTATIONS[round + 1]; // indices after applying round permutation
                    let idx = iter * 5;
                    let _idx0 = pi[idx];
                    let idx1 = pi[idx + 1];
                    let idx2 = pi[idx + 2];
                    let idx3 = pi[idx + 3];
                    let idx4 = pi[idx + 4];
                    [idx1, idx2, idx3, idx4, 25, 26]
                }
                PRECOMPILE_CHI2 if iter < 5 && round < 24 => {
                    let pi = &KECCAK_F1600_PERMUTATIONS[round + 1]; // indices after applying round permutation
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
    const ROUND_CONSTANTS_ADJUSTED: [u64; 25] = KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED;
    let mut keys = Vec::with_capacity(1 << 16);
    for b in 0..1 << 8 {
        for a in 0..1 << 8 {
            let key = [F::from_u32_unchecked(a), F::from_u32_unchecked(b)];
            keys.push(key);
        }
    }
    let table_name = "Keccak Special Xor with Iota Round Constants table".to_string();

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
    let table_name = "AndNot (ie. !a & b) table".to_string();

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
    let table_name = "RotateLeft u16 table".to_string();

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        2,
        |keys| {
            let input = keys[0].as_u32_reduced();
            debug_assert!(input < (1 << 20));

            let word_u16 = input as u16;
            let rot_const = input >> 16;

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

// (index, values) of a control-keyed table row, keyed by control + execute flag or by (control,
// execute). The zero key is padding, with all values zero; column parity also runs in round 24
// (iteration 0) for the delayed iota
fn control_table_row<F: PrimeField, const N: usize>(
    keys: &[F],
    precompile: u32,
    values: impl FnOnce(u32) -> [u32; N],
) -> (usize, ArrayVec<F, 16>) {
    let key = match keys {
        [key] => key.as_u32_reduced(),
        [control, execute] => {
            let (control, execute) = (control.as_u32_reduced(), execute.as_u32_reduced());
            assert!(control < KECCAK_F1600_CONTROL_EXECUTE_FLAG && execute <= 1);
            control | (execute * KECCAK_F1600_CONTROL_EXECUTE_FLAG)
        }
        _ => unreachable!(),
    };
    if key == 0 {
        return (0, [F::ZERO; N].into_iter().collect());
    }
    let control = key ^ KECCAK_F1600_CONTROL_EXECUTE_FLAG;
    assert!(
        control < KECCAK_F1600_CONTROL_EXECUTE_FLAG,
        "control key without execute flag"
    );
    let (row_precompile, iteration, round) = keccak_f1600_decode_control(control);
    assert_eq!(row_precompile, precompile);
    assert!(
        iteration < 5
            && (round < KECCAK_F1600_NUM_ROUNDS
                || (round == KECCAK_F1600_NUM_ROUNDS
                    && iteration == 0
                    && precompile == KECCAK_COLUMN_PARITY_PRECOMPILE))
    );
    (
        1 + round * 5 + iteration,
        values(control)
            .into_iter()
            .map(F::from_u32_unchecked)
            .collect(),
    )
}

// the zero key, then every call of the precompile: control + execute flag (N = 1) or (control,
// execute) (N = 2)
fn keccak_control_keys<F: PrimeField, const N: usize>(precompile: u32) -> Vec<[F; N]> {
    let key = |control: u32, execute: u32| -> [F; N] {
        let key = match N {
            1 => [control | (execute * KECCAK_F1600_CONTROL_EXECUTE_FLAG), 0],
            2 => [control, execute],
            _ => unreachable!(),
        };
        from_fn(|i| F::from_u32_unchecked(key[i]))
    };
    let mut keys = vec![key(0, 0)];
    let mut push = |iteration, round| {
        keys.push(key(
            keccak_f1600_encode_control(precompile, iteration, round),
            1,
        ));
    };
    for round in 0..KECCAK_F1600_NUM_ROUNDS {
        for iteration in 0..5 {
            push(iteration, round);
        }
    }
    if precompile == KECCAK_COLUMN_PARITY_PRECOMPILE {
        push(0, KECCAK_F1600_NUM_ROUNDS);
    }
    keys
}

fn slots<const N: usize>(control: u32) -> [u32; N] {
    let slots = keccak_f1600_slots(control);
    from_fn(|i| slots[i] as u32)
}

pub fn create_keccak_theta_rho_d_indices_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F, 1>(KECCAK_THETA_RHO_PRECOMPILE),
        "keccak theta/rho with in-row D indices".to_string(),
        1,
        KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
        |keys| {
            control_table_row(
                &keys[..1],
                KECCAK_THETA_RHO_PRECOMPILE,
                slots::<KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS>,
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
        &keccak_control_keys::<F, 1>(KECCAK_COLUMN_PARITY_PRECOMPILE),
        "keccak column parity indices".to_string(),
        1,
        KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
        |keys| {
            control_table_row(
                &keys[..1],
                KECCAK_COLUMN_PARITY_PRECOMPILE,
                slots::<KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS>,
            )
        },
        None,
        id,
    )
}

// (control, execute) -> next control and the round whose delayed iota constant applies (0 = none)
// in iteration 0
pub fn create_keccak_column_parity_control_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F, 2>(KECCAK_COLUMN_PARITY_PRECOMPILE),
        "keccak column parity control".to_string(),
        2,
        2,
        |keys| {
            control_table_row(&keys[..2], KECCAK_COLUMN_PARITY_PRECOMPILE, |control| {
                let (_, x, round) = keccak_f1600_decode_control(control);
                let iota_round = if x == 0 { round as u32 } else { 0 };
                [keccak_f1600_bump_control(control), iota_round]
            })
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

// (control, execute) -> next control and one-hot iteration flags
pub fn create_keccak_theta_rho_control_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F, 2>(KECCAK_THETA_RHO_PRECOMPILE),
        "keccak theta/rho control".to_string(),
        2,
        6,
        |keys| {
            control_table_row(&keys[..2], KECCAK_THETA_RHO_PRECOMPILE, |control| {
                let (_, x, _) = keccak_f1600_decode_control(control);
                from_fn::<_, 6, _>(|i| match i {
                    0 => keccak_f1600_bump_control(control),
                    _ => (i - 1 == x) as u32,
                })
            })
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

// keys and values are five nibbles: chi of nibble k of each lane of a plane
pub fn create_keccak_chi5_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let keys: Vec<[F; 5]> = (0..1u32 << 20)
        .map(|key| from_fn(|i| F::from_u32_unchecked((key >> (4 * i)) & 15)))
        .collect();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        "Keccak chi five nibbles".to_owned(),
        5,
        5,
        |key| {
            let n: [u32; 5] = from_fn(|i| key[i].as_u32_reduced());
            let index = (0..5).fold(0, |acc, i| acc | ((n[i] as usize) << (4 * i)));
            let output = (0..5)
                .map(|i| F::from_u32_unchecked(n[i] ^ (!n[(i + 1) % 5] & n[(i + 2) % 5])))
                .collect();
            (index, output)
        },
        None,
        id,
    )
}

// (control, execute) -> next control and the five lane slots
pub fn create_keccak_chi5_control_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keccak_control_keys::<F, 2>(KECCAK_CHI5_PRECOMPILE),
        "Keccak chi control and five indices".to_string(),
        2,
        KECCAK_CHI5_NUM_VARIABLE_OFFSETS + 1,
        |keys| {
            control_table_row(&keys[..2], KECCAK_CHI5_PRECOMPILE, |control| {
                let slots = keccak_f1600_slots(control);
                from_fn::<_, { KECCAK_CHI5_NUM_VARIABLE_OFFSETS + 1 }, _>(|i| match i {
                    0 => keccak_f1600_bump_control(control),
                    _ => slots[i - 1] as u32,
                })
            })
        },
        None,
        id,
    )
}
