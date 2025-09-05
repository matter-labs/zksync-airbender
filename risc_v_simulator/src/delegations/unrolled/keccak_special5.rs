use super::*;
use crate::cycle::state_new::RiscV32StateForUnrolledProver;
use crate::cycle::status_registers::TrapReason;
use common_constants::keccak_special5::*;
use cs::definitions::{TimestampData, TimestampScalar};

pub fn keccak_special5_over_unrolled_state<M: MemorySource, TR: Tracer<C>, C: MachineConfig>(
    machine_state: &mut RiscV32StateForUnrolledProver<C>,
    memory_source: &mut M,
    tracer: &mut TR,
) {
    // read registers first
    let x10 = machine_state.observable.registers[10];
    let x11 = machine_state.observable.registers[11];
    let control = x10 >> 16;
    assert!(
        x10 % (1 << 16) == 0,
        "input control should have lowest 16 bits null"
    );
    assert!(x11 % 256 == 0, "input pointer is unaligned");
    assert!(
        control < 1 << 15,
        "control parameter should be 15 bits but was more"
    );
    assert!(
        x11 >= 1 << 21,
        "state pointer should be in RAM address space but was in ROM"
    );

    // extract control info
    let (precompile, iteration, round) = {
        let precompile_bitmask = control & 0b11111;
        let iteration_bitmask = (control >> 5) & 0b11111;
        let round = control >> 10;
        (
            precompile_bitmask.trailing_zeros(),
            iteration_bitmask.trailing_zeros() as usize,
            round as usize,
        )
    };
    assert!(
        precompile < 5 && iteration < 5 && round < 24,
        "the control parameters are invalid"
    );

    const PRECOMPILE_IOTA_COLUMNXOR: u32 = 0;
    const PRECOMPILE_COLUMNMIX: u32 = 1;
    const PRECOMPILE_THETA_RHO: u32 = 2;
    const PRECOMPILE_CHI1: u32 = 3;
    const PRECOMPILE_CHI2: u32 = 4;

    // update the control register
    let control_next = match precompile {
        PRECOMPILE_IOTA_COLUMNXOR => {
            let iteration_next = (iteration + 1) % 5;
            let precompile_next = if iteration == 4 {
                PRECOMPILE_COLUMNMIX
            } else {
                precompile
            };
            let round_next = round as u32;
            (1 << precompile_next) | (1 << iteration_next) << 5 | round_next << 10
        }
        PRECOMPILE_COLUMNMIX => {
            let iteration_next = iteration;
            let precompile_next = PRECOMPILE_THETA_RHO;
            let round_next = round as u32;
            (1 << precompile_next) | (1 << iteration_next) << 5 | round_next << 10
        }
        PRECOMPILE_THETA_RHO => {
            let iteration_next = (iteration + 1) % 5;
            let precompile_next = if iteration == 4 {
                PRECOMPILE_CHI1
            } else {
                precompile
            };
            let round_next = round as u32;
            (1 << precompile_next) | (1 << iteration_next) << 5 | round_next << 10
        }
        PRECOMPILE_CHI1 => {
            let iteration_next = iteration;
            let precompile_next = PRECOMPILE_CHI2;
            let round_next = round as u32;
            (1 << precompile_next) | (1 << iteration_next) << 5 | round_next << 10
        }
        PRECOMPILE_CHI2 => {
            let iteration_next = (iteration + 1) % 5;
            let precompile_next = if iteration == 4 {
                PRECOMPILE_IOTA_COLUMNXOR
            } else {
                PRECOMPILE_CHI1
            };
            let round_next = if iteration == 4 {
                round as u32 + 1
            } else {
                round as u32
            };
            (1 << precompile_next) | (1 << iteration_next) << 5 | round_next << 10
        }
        _ => unreachable!(),
    };
    let x10_next = control_next << 16;
    machine_state.observable.registers[10] = x10_next;

    // extract state indexes (for address r/w)
    let sparse_access_state_indexes: [usize; KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS] = {
        const PERMUTATIONS_ADJUSTED: [usize; 25 * 25] = {
            let perms = [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2,
                8, 14, 15, 21, 0, 9, 13, 17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11,
                15, 12, 16, 20, 4, 8, 0, 22, 19, 11, 8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18,
                10, 7, 4, 13, 5, 2, 24, 16, 0, 14, 23, 7, 16, 11, 20, 9, 18, 2, 22, 6, 15, 4, 13,
                8, 17, 1, 10, 24, 19, 3, 12, 21, 5, 0, 20, 15, 10, 5, 7, 2, 22, 17, 12, 14, 9, 4,
                24, 19, 16, 11, 6, 1, 21, 23, 18, 13, 8, 3, 0, 2, 4, 1, 3, 10, 12, 14, 11, 13, 20,
                22, 24, 21, 23, 5, 7, 9, 6, 8, 15, 17, 19, 16, 18, 0, 12, 24, 6, 18, 1, 13, 20, 7,
                19, 2, 14, 21, 8, 15, 3, 10, 22, 9, 16, 4, 11, 23, 5, 17, 0, 13, 21, 9, 17, 6, 19,
                2, 10, 23, 12, 20, 8, 16, 4, 18, 1, 14, 22, 5, 24, 7, 15, 3, 11, 0, 19, 8, 22, 11,
                9, 23, 12, 1, 15, 13, 2, 16, 5, 24, 17, 6, 20, 14, 3, 21, 10, 4, 18, 7, 0, 23, 16,
                14, 7, 22, 15, 13, 6, 4, 19, 12, 5, 3, 21, 11, 9, 2, 20, 18, 8, 1, 24, 17, 10, 0,
                15, 5, 20, 10, 14, 4, 19, 9, 24, 23, 13, 3, 18, 8, 7, 22, 12, 2, 17, 16, 6, 21, 11,
                1, 0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9,
                8, 7, 6, 0, 24, 18, 12, 6, 2, 21, 15, 14, 8, 4, 23, 17, 11, 5, 1, 20, 19, 13, 7, 3,
                22, 16, 10, 9, 0, 21, 17, 13, 9, 12, 8, 4, 20, 16, 24, 15, 11, 7, 3, 6, 2, 23, 19,
                10, 18, 14, 5, 1, 22, 0, 8, 11, 19, 22, 13, 16, 24, 2, 5, 21, 4, 7, 10, 18, 9, 12,
                15, 23, 1, 17, 20, 3, 6, 14, 0, 16, 7, 23, 14, 19, 5, 21, 12, 3, 8, 24, 10, 1, 17,
                22, 13, 4, 15, 6, 11, 2, 18, 9, 20, 0, 5, 10, 15, 20, 23, 3, 8, 13, 18, 16, 21, 1,
                6, 11, 14, 19, 24, 4, 9, 7, 12, 17, 22, 2, 0, 3, 1, 4, 2, 15, 18, 16, 19, 17, 5, 8,
                6, 9, 7, 20, 23, 21, 24, 22, 10, 13, 11, 14, 12, 0, 18, 6, 24, 12, 4, 17, 5, 23,
                11, 3, 16, 9, 22, 10, 2, 15, 8, 21, 14, 1, 19, 7, 20, 13, 0, 17, 9, 21, 13, 24, 11,
                3, 15, 7, 18, 5, 22, 14, 1, 12, 4, 16, 8, 20, 6, 23, 10, 2, 19, 0, 11, 22, 8, 19,
                21, 7, 18, 4, 10, 17, 3, 14, 20, 6, 13, 24, 5, 16, 2, 9, 15, 1, 12, 23, 0, 7, 14,
                16, 23, 8, 10, 17, 24, 1, 11, 18, 20, 2, 9, 19, 21, 3, 5, 12, 22, 4, 6, 13, 15, 0,
                10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19,
                4, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                22, 23, 24,
            ];
            let mut i = 0;
            while i < perms.len() {
                assert!(perms[i] < 30);
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
            PRECOMPILE_COLUMNMIX => [25, 26, 27, 28, 29, 0],
            PRECOMPILE_THETA_RHO => {
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
    };

    // read u64 state words
    let state_access_u32_word_offsets = {
        let mut result = [0; KECCAK_SPECIAL5_X11_NUM_WRITES];
        for i in 0..6 {
            result[i * 2] = sparse_access_state_indexes[i] * 2;
            result[i * 2 + 1] = sparse_access_state_indexes[i] * 2 + 1;
        }
        result
    };
    let mut state_accesses: [RegisterOrIndirectReadWriteData; KECCAK_SPECIAL5_X11_NUM_WRITES] =
        register_indirect_read_write_sparse_noexcept::<_, KECCAK_SPECIAL5_X11_NUM_WRITES>(
            x11 as usize,
            state_access_u32_word_offsets,
            memory_source,
        );
    let state_read_addresses: [u32; KECCAK_SPECIAL5_X11_NUM_WRITES] = std::array::from_fn(|i| {
        x11 + (core::mem::size_of::<u32>() * state_access_u32_word_offsets[i]) as u32
    });

    // COMPUTE THE ACTUAL PRECOMPILES
    let state_inputs: [u64; 6] = core::array::from_fn(|i| {
        state_accesses[i * 2].read_value as u64
            | (state_accesses[i * 2 + 1].read_value as u64) << 32
    });
    let state_outputs = match precompile {
        PRECOMPILE_IOTA_COLUMNXOR => {
            let [idx0, idx5, idx10, idx15, idx20, idcol] = state_inputs;
            let idx0_new = {
                let chosen_round_constant = {
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
        PRECOMPILE_COLUMNMIX => {
            let [i25, i26, i27, i28, i29, i0] = state_inputs;
            let i25_new = i25 ^ i27.rotate_left(1);
            let i26_new = i26 ^ i28.rotate_left(1);
            let i27_new = i27 ^ i29.rotate_left(1);
            let i28_new = i28 ^ i25.rotate_left(1);
            let i29_new = i29 ^ i26.rotate_left(1);
            let i0_new = i0;
            [i25_new, i26_new, i27_new, i28_new, i29_new, i0_new]
        }
        PRECOMPILE_THETA_RHO => {
            let [idx0, idx5, idx10, idx15, idx20, idcol] = state_inputs;
            let [rot_idx0, rot_idx5, rot_idx10, rot_idx15, rot_idx20] = match iteration {
                0 => [0, 36, 3, 41, 18],
                1 => [1, 44, 10, 45, 2],
                2 => [62, 6, 43, 15, 61],
                3 => [28, 55, 25, 21, 56],
                4 => [27, 20, 39, 8, 14],
                _ => unreachable!(),
            };
            let idx0_new = (idx0 ^ idcol).rotate_left(rot_idx0);
            let idx5_new = (idx5 ^ idcol).rotate_left(rot_idx5);
            let idx10_new = (idx10 ^ idcol).rotate_left(rot_idx10);
            let idx15_new = (idx15 ^ idcol).rotate_left(rot_idx15);
            let idx20_new = (idx20 ^ idcol).rotate_left(rot_idx20);
            let idcol_new = idcol;
            [
                idx0_new, idx5_new, idx10_new, idx15_new, idx20_new, idcol_new,
            ]
        }
        PRECOMPILE_CHI1 => {
            let [idx1, idx2, idx3, idx4, i25, i26] = state_inputs;
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
            let i27_new = idx0_new;
            [idx0_new, idx3_new, idx4_new, i25_new, i26_new, i27_new]
        }
        _ => unreachable!(),
    };

    // write back into our bookkeeping
    for i in 0..6 {
        state_accesses[i * 2].write_value = state_outputs[i] as u32;
        state_accesses[i * 2 + 1].write_value = (state_outputs[i] >> 32) as u32;
    }

    // write down to RAM
    write_indirect_accesses_sparse_noexcept::<_, KECCAK_SPECIAL5_X11_NUM_WRITES>(
        x11 as usize,
        state_access_u32_word_offsets,
        &state_accesses,
        memory_source,
    );

    // make witness structures - there are no register writes
    let mut register_accesses = [
        RegisterOrIndirectReadWriteData {
            read_value: x10,
            write_value: x10_next,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x11,
            write_value: x11,
            timestamp: TimestampData::EMPTY,
        },
    ];

    tracer.record_delegation(
        KECCAK_SPECIAL5_CSR_REGISTER,
        KECCAK_SPECIAL5_BASE_ABI_REGISTER,
        &mut register_accesses,
        &[],
        &mut [],
        &state_read_addresses,
        &mut state_accesses,
        &sparse_access_state_indexes.map(|x| RegisterOrIndirectVariableOffsetData::from(x as u16)),
    );
}
