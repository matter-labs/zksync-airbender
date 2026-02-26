//! Deterministic helpers for the keccak-specific permutation index tables.
//!
//! These tables are pure functions of the 12-bit `control_with_exe` key used by
//! `keccak_special5`. The LLZK backend uses these helpers in both `@constrain`
//! and `@compute` so the table semantics stay aligned.

use prover::cs::tables::TableType;

const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
const PRECOMPILE_COLUMNMIX1: u32 = 1;
const PRECOMPILE_COLUMNMIX2: u32 = 2;
const PRECOMPILE_THETA: u32 = 3;
const PRECOMPILE_RHO: u32 = 4;
const PRECOMPILE_CHI1: u32 = 5;
const PRECOMPILE_CHI2: u32 = 6;

const PERMUTATIONS_ADJUSTED: [u64; 25 * 25] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 6,
    12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21, 0, 9, 13,
    17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11, 15, 12, 16, 20, 4, 8, 0, 22, 19, 11,
    8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18, 10, 7, 4, 13, 5, 2, 24, 16, 0, 14, 23, 7, 16,
    11, 20, 9, 18, 2, 22, 6, 15, 4, 13, 8, 17, 1, 10, 24, 19, 3, 12, 21, 5, 0, 20, 15, 10, 5, 7, 2,
    22, 17, 12, 14, 9, 4, 24, 19, 16, 11, 6, 1, 21, 23, 18, 13, 8, 3, 0, 2, 4, 1, 3, 10, 12, 14,
    11, 13, 20, 22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 0, 12, 24, 6, 18, 1, 13, 20, 7,
    19, 2, 14, 21, 8, 15, 3, 10, 22, 9, 16, 4, 11, 23, 5, 17, 0, 13, 21, 9, 17, 6, 19, 2, 10, 23,
    12, 20, 8, 16, 4, 18, 1, 14, 22, 5, 24, 7, 15, 3, 11, 0, 19, 8, 22, 11, 9, 23, 12, 1, 15, 13,
    2, 16, 5, 24, 17, 6, 20, 14, 3, 21, 10, 4, 18, 7, 0, 23, 16, 14, 7, 22, 15, 13, 6, 4, 19, 12,
    5, 3, 21, 11, 9, 2, 20, 18, 8, 1, 24, 17, 10, 0, 15, 5, 20, 10, 14, 4, 19, 9, 24, 23, 13, 3,
    18, 8, 7, 22, 12, 2, 17, 16, 6, 21, 11, 1, 0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19, 18, 17,
    16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 0, 24, 18, 12, 6, 2, 21, 15, 14, 8, 4, 23, 17, 11, 5, 1,
    20, 19, 13, 7, 3, 22, 16, 10, 9, 0, 21, 17, 13, 9, 12, 8, 4, 20, 16, 24, 15, 11, 7, 3, 6, 2,
    23, 19, 10, 18, 14, 5, 1, 22, 0, 8, 11, 19, 22, 13, 16, 24, 2, 5, 21, 4, 7, 10, 18, 9, 12, 15,
    23, 1, 17, 20, 3, 6, 14, 0, 16, 7, 23, 14, 19, 5, 21, 12, 3, 8, 24, 10, 1, 17, 22, 13, 4, 15,
    6, 11, 2, 18, 9, 20, 0, 5, 10, 15, 20, 23, 3, 8, 13, 18, 16, 21, 1, 6, 11, 14, 19, 24, 4, 9, 7,
    12, 17, 22, 2, 0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8, 6, 9, 7, 20, 23, 21, 24, 22, 10, 13,
    11, 14, 12, 0, 18, 6, 24, 12, 4, 17, 5, 23, 11, 3, 16, 9, 22, 10, 2, 15, 8, 21, 14, 1, 19, 7,
    20, 13, 0, 17, 9, 21, 13, 24, 11, 3, 15, 7, 18, 5, 22, 14, 1, 12, 4, 16, 8, 20, 6, 23, 10, 2,
    19, 0, 11, 22, 8, 19, 21, 7, 18, 4, 10, 17, 3, 14, 20, 6, 13, 24, 5, 16, 2, 9, 15, 1, 12, 23,
    0, 7, 14, 16, 23, 8, 10, 17, 24, 1, 11, 18, 20, 2, 9, 19, 21, 3, 5, 12, 22, 4, 6, 13, 15, 0,
    10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4, 0, 1, 2,
    3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
];

pub(crate) fn keccak_permutation_indices_outputs(
    table: TableType,
    control_with_exe: u64,
) -> (u64, u64) {
    debug_assert!(control_with_exe < (1 << 12));

    let ij = match table {
        TableType::KeccakPermutationIndices12 => (0usize, 1usize),
        TableType::KeccakPermutationIndices34 => (2usize, 3usize),
        TableType::KeccakPermutationIndices56 => (4usize, 5usize),
        _ => panic!("not a keccak permutation indices table: {table:?}"),
    };

    let control = control_with_exe & 0b0111_1111_1111;
    let exe = (control_with_exe >> 11) == 1;
    let precompile = control as u32 & 0b111;
    let iter = (control as usize >> 3) & 0b111;
    let round = control as usize >> 6;

    let indices = match precompile {
        PRECOMPILE_IOTA_COLUMNXOR if iter < 5 && round <= 24 && exe => {
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25];
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
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25];
            let idcol = IDCOLS[iter];
            let idx0 = pi[iter];
            let idx5 = pi[iter + 5];
            let idx10 = pi[iter + 10];
            let idx15 = pi[iter + 15];
            let idx20 = pi[iter + 20];
            [idx0, idx5, idx10, idx15, idx20, idcol]
        }
        PRECOMPILE_RHO if iter < 5 && round < 24 => {
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..][..25];
            let idx0 = pi[iter];
            let idx5 = pi[iter + 5];
            let idx10 = pi[iter + 10];
            let idx15 = pi[iter + 15];
            let idx20 = pi[iter + 20];
            [idx0, idx5, idx10, idx15, idx20, 25]
        }
        PRECOMPILE_CHI1 if iter < 5 && round < 24 => {
            let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..][..25];
            let idx = iter * 5;
            let idx1 = pi[idx + 1];
            let idx2 = pi[idx + 2];
            let idx3 = pi[idx + 3];
            let idx4 = pi[idx + 4];
            [idx1, idx2, idx3, idx4, 25, 26]
        }
        PRECOMPILE_CHI2 if iter < 5 && round < 24 => {
            let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..][..25];
            let idx = iter * 5;
            let idx0 = pi[idx];
            let idx3 = pi[idx + 3];
            let idx4 = pi[idx + 4];
            [idx0, idx3, idx4, 25, 26, 27]
        }
        0 if iter == 0 && round == 0 => [0, 0, 0, 0, 0, 0],
        _ => [0, 1, 2, 3, 4, 5],
    };

    (indices[ij.0], indices[ij.1])
}
