// Keccak-f1600 as 361 calls into three circuits over keccak_special5's 31-slot state layout.
use super::*;
use common_constants::delegation_types::keccak_f1600::*;

pub(crate) const KECCAK_F1600_PERMUTATIONS: [[usize; 25]; 25] = {
    const FLAT: [usize; 625] = [
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
    let mut result = [[0usize; 25]; 25];
    let mut i = 0;
    while i < 625 {
        result[i / 25][i % 25] = FLAT[i];
        i += 1;
    }
    result
};

pub(crate) const KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED: [u64; 25] = [
    0,
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

pub(crate) const KECCAK_F1600_RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

pub const KECCAK_F1600_INITIAL_CONTROL_VALUE: u32 = 0;
pub const KECCAK_F1600_FINAL_CONTROL_VALUE: u32 = 1 << 3 | 24 << 6;

#[inline(always)]
pub(crate) const fn keccak_f1600_decode_control(control: u32) -> (u32, usize, usize) {
    (
        control & 0b111,
        ((control >> 3) & 0b111) as usize,
        (control >> 6) as usize,
    )
}

#[inline(always)]
pub(crate) const fn keccak_f1600_encode_control(precompile: u32, x: usize, round: usize) -> u32 {
    precompile | (x as u32) << 3 | (round as u32) << 6
}

pub(crate) const fn keccak_f1600_csr_for_precompile(precompile: u32) -> u32 {
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => KECCAK_COLUMN_PARITY_CSR_REGISTER,
        KECCAK_THETA_RHO_PRECOMPILE => KECCAK_THETA_RHO_CSR_REGISTER,
        KECCAK_CHI5_PRECOMPILE => KECCAK_CHI5_CSR_REGISTER,
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

#[inline(always)]
pub(crate) const fn keccak_f1600_bump_control(control: u32) -> u32 {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    if x < 4 {
        return keccak_f1600_encode_control(precompile, x + 1, round);
    }
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_THETA_RHO_PRECOMPILE, 0, round)
        }
        KECCAK_THETA_RHO_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_CHI5_PRECOMPILE, 0, round)
        }
        KECCAK_CHI5_PRECOMPILE => {
            keccak_f1600_encode_control(KECCAK_COLUMN_PARITY_PRECOMPILE, 0, round + 1)
        }
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

// u64 slots of one call, in the circuit's access order; unused entries are 31
pub(crate) const fn keccak_f1600_slots(control: u32) -> [usize; 7] {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    let mut slots = [31usize; 7];
    let mut y = 0;
    match precompile {
        KECCAK_CHI5_PRECOMPILE => {
            while y < 5 {
                slots[y] = KECCAK_F1600_PERMUTATIONS[round + 1][5 * x + y];
                y += 1;
            }
        }
        _ => {
            while y < 5 {
                slots[y] = KECCAK_F1600_PERMUTATIONS[round][x + 5 * y];
                y += 1;
            }
            if precompile == KECCAK_COLUMN_PARITY_PRECOMPILE {
                slots[5] = 25 + x;
            } else {
                slots[5] = 25 + (x + 4) % 5;
                slots[6] = 25 + (x + 1) % 5;
            }
        }
    }
    slots
}

pub(crate) const fn keccak_f1600_num_slots(precompile: u32) -> usize {
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
        KECCAK_THETA_RHO_PRECOMPILE => KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
        _ => KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
    }
}

#[inline(always)]
pub(crate) fn keccak_f1600_apply(state: &mut [u64; 31], control: u32) {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    let slots = keccak_f1600_slots(control);
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => {
            if x == 0 {
                state[slots[0]] ^= KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round];
            }
            state[slots[5]] = state[slots[0]]
                ^ state[slots[1]]
                ^ state[slots[2]]
                ^ state[slots[3]]
                ^ state[slots[4]];
        }
        KECCAK_THETA_RHO_PRECOMPILE => {
            let d = state[slots[5]] ^ state[slots[6]].rotate_left(1);
            for y in 0..5 {
                state[slots[y]] = (state[slots[y]] ^ d).rotate_left(KECCAK_F1600_RHO[x][y]);
            }
        }
        KECCAK_CHI5_PRECOMPILE => {
            let a: [u64; 5] = core::array::from_fn(|k| state[slots[k]]);
            for k in 0..5 {
                state[slots[k]] = a[k] ^ (!a[(k + 1) % 5] & a[(k + 2) % 5]);
            }
        }
        _ => panic!("not a Keccak-f1600 precompile"),
    }
}

// timestamp offset of the last call touching each slot; slot 30 is never touched
pub(crate) const KECCAK_F1600_FINAL_TIMESTAMP_OFFSETS: [Option<u64>; 31] = const {
    let mut result = [None; 31];
    let mut control = KECCAK_F1600_INITIAL_CONTROL_VALUE;
    let mut call = 0;
    while call < NUM_KECCAK_F1600_CALLS {
        let (precompile, _, _) = keccak_f1600_decode_control(control);
        assert!(keccak_f1600_csr_for_precompile(precompile) == keccak_f1600_call_csr(call));
        let slots = keccak_f1600_slots(control);
        let mut j = 0;
        while j < keccak_f1600_num_slots(precompile) {
            result[slots[j]] = Some((call as u64) * TIMESTAMP_STEP);
            j += 1;
        }
        control = keccak_f1600_bump_control(control);
        call += 1;
    }
    assert!(control == KECCAK_F1600_FINAL_CONTROL_VALUE);
    let mut i = 0;
    while i < 30 {
        assert!(result[i].is_some());
        i += 1;
    }
    assert!(result[30].is_none());
    result
};

const RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

fn keccak_round(state: &mut [u64; 31], round: usize) {
    let mut array = [0u64; 5];
    for x in 0..5 {
        for y in 0..5 {
            array[x] ^= state[5 * y + x];
        }
    }
    for x in 0..5 {
        let t = array[(x + 4) % 5] ^ array[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            state[5 * y + x] ^= t;
        }
    }
    let mut last = state[1];
    for x in 0..24 {
        array[0] = state[PI[x]];
        state[PI[x]] = last.rotate_left(RHO[x]);
        last = array[0];
    }
    for y_step in 0..5 {
        let y = 5 * y_step;
        for x in 0..5 {
            array[x] = state[y + x];
        }
        for x in 0..5 {
            state[y + x] = array[x] ^ (!array[(x + 1) % 5] & array[(x + 2) % 5]);
        }
    }
    state[0] ^= KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round + 1];
}

// the state after all 361 calls: lanes as keccak_f1600, slots 26..29 the column parities entering
// round 23, slot 25 the final state's column 0 parity, slot 30 unchanged
pub(crate) fn keccak_f1600_delegation_impl(state: &mut [u64; 31]) {
    for round in 0..23 {
        keccak_round(state, round);
    }
    for x in 1..5 {
        state[25 + x] = (0..5).fold(0, |acc, y| acc ^ state[5 * y + x]);
    }
    keccak_round(state, 23);
    state[25] = (0..5).fold(0, |acc, y| acc ^ state[5 * y]);
}

pub(crate) const KECCAK_F1600_ACCESSED_SLOTS: usize = 30;

#[inline(never)]
pub(crate) fn keccak_f1600_call<C: Counters, S: Snapshotter<C>, R: RAM, E: ExecutionObserver<C>>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
) {
    const LAST_CALL_OFFSET: TimestampScalar =
        ((NUM_KECCAK_F1600_CALLS - 1) as TimestampScalar) * TIMESTAMP_STEP;
    let x10 = state.registers[10].value;
    let x11 = state.registers[11].value;
    debug_assert_eq!(state.timestamp % 4, 0);
    assert!(
        x11 as usize >= common_constants::rom::ROM_BYTE_SIZE,
        "state ptr is not in RAM"
    );
    assert_eq!(x11 % 256, 0, "state ptr is not aligned");
    assert_eq!(x10, KECCAK_F1600_INITIAL_CONTROL_VALUE);

    state.registers[10].value = KECCAK_F1600_FINAL_CONTROL_VALUE;
    state.registers[10].timestamp = state.timestamp + LAST_CALL_OFFSET + 3;
    state.registers[11].timestamp = state.timestamp + LAST_CALL_OFFSET + 3;
    state.registers[0].timestamp = (state.timestamp + LAST_CALL_OFFSET) | 2;

    let write_ts_base = state.timestamp | 3;
    let mut local_state = [0u64; 31];
    let mut addr = x11;
    for i in 0..KECCAK_F1600_ACCESSED_SLOTS {
        let low_value = ram.peek_word(addr);
        let high_value = ram.peek_word(addr + 4);
        addr += 8;
        local_state[i] = (low_value as u64) | ((high_value as u64) << 32);
    }
    keccak_f1600_delegation_impl(&mut local_state);
    let mut addr = x11;
    for i in 0..KECCAK_F1600_ACCESSED_SLOTS {
        let value = local_state[i];
        let write_ts = write_ts_base + KECCAK_F1600_FINAL_TIMESTAMP_OFFSETS[i].unwrap();
        let (ts, old_value) = ram.write_word(addr, value as u32, write_ts);
        snapshotter.append_memory_read(addr, old_value, ts, write_ts);
        let (ts, old_value) = ram.write_word(addr + 4, (value >> 32) as u32, write_ts);
        snapshotter.append_memory_read(addr + 4, old_value, ts, write_ts);
        addr += 8;
    }

    state.timestamp += LAST_CALL_OFFSET;
    state.counters.bump_keccak_f1600(NUM_KECCAK_F1600_CALLS);
    E::on_delegation(
        state,
        KECCAK_COLUMN_PARITY_CSR_REGISTER,
        NUM_KECCAK_F1600_CALLS as u64,
    );
    state.pc = state
        .pc
        .wrapping_add((core::mem::size_of::<u32>() * NUM_KECCAK_F1600_CALLS) as u32);
    state
        .counters
        .log_multiple_circuit_family_calls::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
            NUM_KECCAK_F1600_CALLS,
        );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pseudo_random_state(seed: u64) -> [u64; 31] {
        let mut v = seed ^ 0x9E3779B97F4A7C15;
        core::array::from_fn(|_| {
            v ^= v << 13;
            v ^= v >> 7;
            v ^= v << 17;
            v
        })
    }

    #[test]
    fn fast_path_matches_call_by_call_execution() {
        for seed in 0..4 {
            let initial = if seed == 0 {
                [0u64; 31]
            } else {
                pseudo_random_state(seed)
            };
            let mut stepped = initial;
            let mut control = KECCAK_F1600_INITIAL_CONTROL_VALUE;
            for _ in 0..NUM_KECCAK_F1600_CALLS {
                keccak_f1600_apply(&mut stepped, control);
                control = keccak_f1600_bump_control(control);
            }
            assert_eq!(control, KECCAK_F1600_FINAL_CONTROL_VALUE);
            let mut fast = initial;
            keccak_f1600_delegation_impl(&mut fast);
            assert_eq!(fast, stepped, "seed {seed}");
            if seed == 0 {
                assert_eq!(fast[0], 0xF1258F7940E1DDE7);
                assert_eq!(fast[1], 0x84D5CCF933C0478A);
            }
        }
    }
}
