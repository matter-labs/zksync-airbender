use super::*;
use common_constants::*;

const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
const PRECOMPILE_COLUMNMIX1: u32 = 1;
const PRECOMPILE_COLUMNMIX2: u32 = 2;
const PRECOMPILE_THETA: u32 = 3;
const PRECOMPILE_RHO: u32 = 4;
const PRECOMPILE_CHI1: u32 = 5;
const PRECOMPILE_CHI2: u32 = 6;

#[inline(always)]
fn peek_u64_words<R: RAM, const N: usize>(
    addr_base: usize,
    offsets: [usize; N],
    ram: &R,
) -> [u64; N] {
    core::array::from_fn(|i| {
        let offset = offsets[i];
        let addr_low = (addr_base + offset * core::mem::size_of::<u64>()) as u32;
        let addr_high =
            (addr_base + offset * core::mem::size_of::<u64>() + core::mem::size_of::<u32>()) as u32;
        let low = ram.peek_word(addr_low);
        let high = ram.peek_word(addr_high);
        low as u64 | (high as u64) << 32
    })
}

#[inline(always)]
fn write_u64_words<C: Counters, S: Snapshotter<C>, R: RAM, const N: usize>(
    addr_base: usize,
    offsets: [usize; N],
    values: [u64; N],
    ram: &mut R,
    snapshotter: &mut S,
    write_timestamp: TimestampScalar,
) {
    for i in 0..N {
        let offset = offsets[i];
        let value = values[i];
        let low = value as u32;
        let high = (value >> 32) as u32;
        let addr_low = (addr_base + offset * core::mem::size_of::<u64>()) as u32;
        let addr_high =
            (addr_base + offset * core::mem::size_of::<u64>() + core::mem::size_of::<u32>()) as u32;
        let (read_timestamp, old_value) = ram.write_word(addr_low, low, write_timestamp);
        snapshotter.append_memory_read(addr_low, old_value, read_timestamp, write_timestamp);
        let (read_timestamp, old_value) = ram.write_word(addr_high, high, write_timestamp);
        snapshotter.append_memory_read(addr_low, old_value, read_timestamp, write_timestamp);
    }
}

#[inline(never)]
pub(crate) fn keccak_special5_call<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
) {
    let x10 = state.registers[10].value; // don't process it just yet, wait for write!
    let x11 = read_register::<C, 3>(state, 11);
    assert!(x11 >= 1 << 21, "state ptr is not in RAM");
    assert!(x10 < 1 << 11, "control info is too big");
    assert!(x11 % 256 == 0, "state ptr is not aligned");

    // get control
    let control = x10;
    let (precompile, iteration, round) = keccak_special5_impl_decode_control(control);

    // update control
    let control_next = keccak_special5_impl_bump_control(precompile, iteration, round);
    let mut x10_next = control_next;
    write_register::<C, 3>(state, 10, &mut x10_next); // extremely strange &mut

    // get indexes
    let state_indexes = keccak_special5_impl_extract_indices(precompile, iteration, round);

    // get inputs
    let state_inputs = peek_u64_words(x11 as usize, state_indexes, ram);

    // get outputs
    let state_outputs =
        keccak_special5_impl_compute_outputs(precompile, iteration, round, state_inputs);

    // write RAM
    let write_timestamp = state.timestamp | 3;
    write_u64_words(
        x11 as usize,
        state_indexes,
        state_outputs,
        ram,
        snapshotter,
        write_timestamp,
    );

    state.counters.bump_keccak_special5();
}

#[inline(always)]
pub(crate) fn keccak_special5_impl_decode_control(control: u32) -> (u32, usize, usize) {
    let precompile = control & 0b111;
    let iteration = ((control >> 3) & 0b111) as usize;
    let round = (control >> 6) as usize;
    assert!(
        (precompile < 7 && iteration < 5 && round < 24)
            || (precompile == 0 && iteration < 5 && round <= 24),
        "the control parameters are invalid"
    );
    (precompile, iteration, round)
}

#[inline(always)]
pub(crate) fn keccak_special5_impl_bump_control(
    precompile: u32,
    iteration: usize,
    round: usize,
) -> u32 {
    let (precompile_next, iteration_next, round_next) = match precompile {
        PRECOMPILE_IOTA_COLUMNXOR | PRECOMPILE_THETA | PRECOMPILE_RHO => {
            let precompile_next = if iteration == 4 {
                precompile + 1
            } else {
                precompile
            };
            let iteration_next = (iteration + 1) % 5;
            let round_next = round;
            (precompile_next, iteration_next, round_next)
        }
        PRECOMPILE_COLUMNMIX1 | PRECOMPILE_COLUMNMIX2 | PRECOMPILE_CHI1 => {
            let precompile_next = precompile + 1;
            let iteration_next = iteration;
            let round_next = round;
            (precompile_next, iteration_next, round_next)
        }
        PRECOMPILE_CHI2 => {
            let precompile_next = if iteration == 4 {
                PRECOMPILE_IOTA_COLUMNXOR
            } else {
                precompile - 1
            };
            let iteration_next = (iteration + 1) % 5;
            let round_next = if iteration == 4 { round + 1 } else { round };
            (precompile_next, iteration_next, round_next)
        }
        _ => unreachable!(),
    };
    precompile_next | (iteration_next as u32) << 3 | (round_next as u32) << 6
}

#[inline(always)]
pub(crate) fn keccak_special5_impl_extract_indices(
    precompile: u32,
    iteration: usize,
    round: usize,
) -> [usize; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS] {
    const PERMUTATIONS_ADJUSTED: [usize; 25 * 25] = {
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
            assert!(perms[i] < 25);
            i += 1;
        }
        perms
    };
    match precompile {
        PRECOMPILE_IOTA_COLUMNXOR => {
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..]; // indices before applying round permutation
            let idcol = 25 + iteration;
            let idx0 = pi[iteration];
            let idx5 = pi[iteration + 5];
            let idx10 = pi[iteration + 10];
            let idx15 = pi[iteration + 15];
            let idx20 = pi[iteration + 20];
            [idx0, idx5, idx10, idx15, idx20, idcol]
        }
        PRECOMPILE_COLUMNMIX1 => [25, 26, 27, 28, 29, 30],
        PRECOMPILE_COLUMNMIX2 => [25, 26, 27, 28, 29, 30],
        PRECOMPILE_THETA => {
            const IDCOLS: [usize; 5] = [29, 25, 26, 27, 28];
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..]; // indices before applying round permutation
            let idcol = IDCOLS[iteration];
            let idx0 = pi[iteration];
            let idx5 = pi[iteration + 5];
            let idx10 = pi[iteration + 10];
            let idx15 = pi[iteration + 15];
            let idx20 = pi[iteration + 20];
            [idx0, idx5, idx10, idx15, idx20, idcol]
        }
        PRECOMPILE_RHO => {
            let pi = &PERMUTATIONS_ADJUSTED[round * 25..]; // indices before applying round permutation
            let idx0 = pi[iteration];
            let idx5 = pi[iteration + 5];
            let idx10 = pi[iteration + 10];
            let idx15 = pi[iteration + 15];
            let idx20 = pi[iteration + 20];
            [idx0, idx5, idx10, idx15, idx20, 25]
        }
        PRECOMPILE_CHI1 => {
            let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..]; // indices after applying round permutation
            let idx = iteration * 5;
            let _idx0 = pi[idx];
            let idx1 = pi[idx + 1];
            let idx2 = pi[idx + 2];
            let idx3 = pi[idx + 3];
            let idx4 = pi[idx + 4];
            [idx1, idx2, idx3, idx4, 25, 26]
        }
        PRECOMPILE_CHI2 => {
            let pi = &PERMUTATIONS_ADJUSTED[(round + 1) * 25..]; // indices after applying round permutation
            let idx = iteration * 5;
            let idx0 = pi[idx];
            let _idx1 = pi[idx + 1];
            let _idx2 = pi[idx + 2];
            let idx3 = pi[idx + 3];
            let idx4 = pi[idx + 4];
            [idx0, idx3, idx4, 25, 26, 27]
        }
        _ => unreachable!("this is a junk scenario"),
    }
}

#[inline(always)]
pub(crate) fn keccak_special5_impl_compute_outputs(
    precompile: u32,
    iteration: usize,
    round: usize,
    state_inputs: [u64; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS],
) -> [u64; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS] {
    match precompile {
        PRECOMPILE_IOTA_COLUMNXOR => {
            let [idx0, idx5, idx10, idx15, idx20, _idcol] = state_inputs;
            let idx0_new = {
                let chosen_round_constant = {
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
                        9223372039002292232,
                    ];
                    let round_if_iter0 = if iteration == 0 { round } else { 0 };
                    ROUND_CONSTANTS_ADJUSTED[round_if_iter0]
                };
                idx0 ^ chosen_round_constant
            };
            let idx5_new = idx5;
            let idx10_new = idx10;
            let idx15_new = idx15;
            let idx20_new = idx20;
            let idcol_new = idx0_new ^ idx5 ^ idx10 ^ idx15 ^ idx20;
            [
                idx0_new, idx5_new, idx10_new, idx15_new, idx20_new, idcol_new,
            ]
        }
        PRECOMPILE_COLUMNMIX1 => {
            let [i25, i26, i27, i28, i29, _i30] = state_inputs;
            let i25_new = i25 ^ i27.rotate_left(1);
            let i26_new = i26;
            let i27_new = i27 ^ i29.rotate_left(1);
            let i28_new = i28;
            let i29_new = i29;
            let i30_new = i25.rotate_left(1);
            [i25_new, i26_new, i27_new, i28_new, i29_new, i30_new]
        }
        PRECOMPILE_COLUMNMIX2 => {
            let [i25, i26, i27, i28, i29, i30] = state_inputs;
            let i25_new = i25;
            let i26_new = i26 ^ i28.rotate_left(1);
            let i27_new = i27;
            let i28_new = i28 ^ i30;
            let i29_new = i29 ^ i26.rotate_left(1);
            let i30_new = i30;
            [i25_new, i26_new, i27_new, i28_new, i29_new, i30_new]
        }
        PRECOMPILE_THETA => {
            let [idx0, idx5, idx10, idx15, idx20, idcol] = state_inputs;
            let idx0_new = idx0 ^ idcol;
            let idx5_new = idx5 ^ idcol;
            let idx10_new = idx10 ^ idcol;
            let idx15_new = idx15 ^ idcol;
            let idx20_new = idx20 ^ idcol;
            let idcol_new = idcol;
            [
                idx0_new, idx5_new, idx10_new, idx15_new, idx20_new, idcol_new,
            ]
        }
        PRECOMPILE_RHO => {
            let [idx0, idx5, idx10, idx15, idx20, i25] = state_inputs;
            let [rot_idx0, rot_idx5, rot_idx10, rot_idx15, rot_idx20] = match iteration {
                0 => [0, 36, 3, 41, 18],
                1 => [1, 44, 10, 45, 2],
                2 => [62, 6, 43, 15, 61],
                3 => [28, 55, 25, 21, 56],
                4 => [27, 20, 39, 8, 14],
                _ => unreachable!(),
            };
            let idx0_new = idx0.rotate_left(rot_idx0);
            let idx5_new = idx5.rotate_left(rot_idx5);
            let idx10_new = idx10.rotate_left(rot_idx10);
            let idx15_new = idx15.rotate_left(rot_idx15);
            let idx20_new = idx20.rotate_left(rot_idx20);
            let i25_new = i25;
            [idx0_new, idx5_new, idx10_new, idx15_new, idx20_new, i25_new]
        }
        PRECOMPILE_CHI1 => {
            let [idx1, idx2, idx3, idx4, _i25, _i26] = state_inputs;
            let idx1_new = idx1 ^ (!idx2 & idx3);
            let idx2_new = idx2 ^ (!idx3 & idx4);
            let idx3_new = idx3;
            let idx4_new = idx4;
            let i25_new = !idx1 & idx2;
            let i26_new = idx1;
            [idx1_new, idx2_new, idx3_new, idx4_new, i25_new, i26_new]
        }
        PRECOMPILE_CHI2 => {
            let [idx0, idx3, idx4, i25, i26, i27] = state_inputs;
            let idx0_new = idx0 ^ i25;
            let idx3_new = idx3 ^ (!idx4 & idx0);
            let idx4_new = idx4 ^ (!idx0 & i26);
            let i25_new = i25;
            let i26_new = i26;
            let i27_new = i27;
            [idx0_new, idx3_new, idx4_new, i25_new, i26_new, i27_new]
        }
        _ => unreachable!(),
    }
}
