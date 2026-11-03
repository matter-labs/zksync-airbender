// Keccak-f1600 as 361 calls into three circuits over keccak_special5's 31-slot state layout.
use super::keccak_special5::{PI, RHO};
use super::*;
use common_constants::delegation_types::keccak_f1600::*;
use common_constants::KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS;

#[inline(always)]
pub(crate) fn keccak_f1600_apply(
    state: &mut [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS],
    control: u32,
) {
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

// timestamp offset of the last call touching each slot
pub(crate) const KECCAK_F1600_FINAL_TIMESTAMP_OFFSETS: [u64; KECCAK_F1600_ACCESSED_SLOTS] = const {
    let mut result = [u64::MAX; KECCAK_F1600_ACCESSED_SLOTS];
    let mut control = KECCAK_F1600_INITIAL_CONTROL_VALUE;
    let mut call = 0;
    while call < NUM_KECCAK_F1600_CALLS {
        let (precompile, _, _) = keccak_f1600_decode_control(control);
        let slots = keccak_f1600_slots(control);
        let mut j = 0;
        while j < keccak_f1600_num_slots(precompile) {
            result[slots[j]] = (call as u64) * TIMESTAMP_STEP;
            j += 1;
        }
        control = keccak_f1600_bump_control(control);
        call += 1;
    }
    let mut i = 0;
    while i < KECCAK_F1600_ACCESSED_SLOTS {
        assert!(result[i] != u64::MAX);
        i += 1;
    }
    result
};

fn keccak_round(state: &mut [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS], round: usize) {
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
        array.copy_from_slice(&state[y..y + 5]);
        for x in 0..5 {
            state[y + x] = array[x] ^ (!array[(x + 1) % 5] & array[(x + 2) % 5]);
        }
    }
    state[0] ^= KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round + 1];
}

// the state after all 361 calls: lanes as keccak_f1600, slots 26..29 the column parities entering
// round 23, slot 25 the final state's column 0 parity, slot 30 unchanged
pub(crate) fn keccak_f1600_delegation_impl(
    state: &mut [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS],
) {
    for round in 0..KECCAK_F1600_NUM_ROUNDS - 1 {
        keccak_round(state, round);
    }
    for x in 1..5 {
        state[KECCAK_F1600_PARITY_SLOT_OFFSET + x] =
            (0..5).fold(0, |acc, y| acc ^ state[5 * y + x]);
    }
    keccak_round(state, KECCAK_F1600_NUM_ROUNDS - 1);
    state[KECCAK_F1600_PARITY_SLOT_OFFSET] = (0..5).fold(0, |acc, y| acc ^ state[5 * y]);
}

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
    let mut local_state = [0u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS];
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
        let write_ts = write_ts_base + KECCAK_F1600_FINAL_TIMESTAMP_OFFSETS[i];
        let (ts, old_value) = ram.write_word(addr, value as u32, write_ts);
        snapshotter.append_memory_read(addr, old_value, ts, write_ts);
        let (ts, old_value) = ram.write_word(addr + 4, (value >> 32) as u32, write_ts);
        snapshotter.append_memory_read(addr + 4, old_value, ts, write_ts);
        addr += 8;
    }

    state.timestamp += LAST_CALL_OFFSET;
    state.counters.bump_keccak_f1600(NUM_KECCAK_F1600_CALLS);
    for call in 0..NUM_KECCAK_F1600_CALLS {
        E::on_delegation(state, keccak_f1600_call_csr(call), 1);
    }
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

    fn pseudo_random_state(seed: u64) -> [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS] {
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
                [0u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS]
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
