use std::mem::MaybeUninit;

use super::*;
use blake2s_u32::g_function_control_flags::*;
use blake2s_u32::state_with_extended_control::Blake2RoundFunctionEvaluator;
use blake2s_u32::*;
use common_constants::*;

pub const MIXING_FUNCTION_ACCESS_IDXES: [[usize; 4]; BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

pub const STATE_EL_INTO_MIXING_FUNCTION_ROUND: [usize; 16] = const {
    let mut result = [0; 16];
    let mut i = 0;
    while i < MIXING_FUNCTION_ACCESS_IDXES.len() {
        let [a, b, c, d] = MIXING_FUNCTION_ACCESS_IDXES[i];
        result[a] = i;
        result[b] = i;
        result[c] = i;
        result[d] = i;
        i += 1;
    }

    result
};

pub(crate) const REDUCED_ROUNDS_SIGMA_INV: [usize; 16] =
    sigma_pairs_into_g_function_number(SIGMAS_BY_PAIRS[6]);
pub(crate) const FULL_ROUNDS_SIGMA_INV: [usize; 16] =
    sigma_pairs_into_g_function_number(SIGMAS_BY_PAIRS[9]);

const fn sigma_pairs_into_g_function_number(sigma_pairs: [[usize; 2]; 8]) -> [usize; 16] {
    let mut result = [0; 16];
    let mut i = 0;
    while i < sigma_pairs.len() {
        let [x, y] = sigma_pairs[i];
        result[x] = i;
        result[y] = i;
        i += 1;
    }

    result
}

#[inline(never)]
pub(crate) fn blake2_g_function_call<
    C: Counters,
    S: Snapshotter<C>,
    R: RAM,
    E: ExecutionObserver<C>,
>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
) {
    let x10 = state.registers[10].value;
    let x11 = state.registers[11].value;
    let x12 = state.registers[12].value;

    assert!(
        x10 >= common_constants::rom::ROM_BYTE_SIZE as u32,
        "state pointer is in ROM"
    );
    assert!(
        x11 >= common_constants::rom::ROM_BYTE_SIZE as u32,
        "input pointer is in ROM"
    );

    assert!(x10 != x11);

    assert!(x10 % 64 == 0, "state pointer is unaligned");
    assert!(x11 % 64 == 0, "input pointer is unaligned");

    assert!(
        x12 < (1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS),
        "control register 0x{:08x} is too large",
        x12
    );

    let control_bitmask = x12 >> BLAKE2S_G_FUNCTION_COUNTER_BITS;
    let counter = x12 & ((1 << BLAKE2S_G_FUNCTION_COUNTER_BITS) - 1);

    assert_eq!(counter, 0, "invoked in the middle of round function");

    let reduced_rounds = control_bitmask & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;

    let _num_rounds = if reduced_rounds { 7 } else { 10 };
    let num_invocations = _num_rounds * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;

    let final_x12 = control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS;

    // we run full round function

    state.registers[10].timestamp =
        state.timestamp + ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[11].timestamp =
        state.timestamp + ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].timestamp =
        state.timestamp + ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].value = final_x12;

    // NOTE: we should touch x0 and give it a timestamp that would be at the very end of execution
    state.registers[0].timestamp =
        (state.timestamp + ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP) | 2;

    unsafe {
        // read blake state, and input in full for speed, and for purposes of replayer it's also sufficient - replayer
        // can generate indexes of real accesses in the proper order (timestamps will be a little more painful, but not more than keccak)

        // NOTE: even though we use the same structure as full round function, we only need extended(!) state
        let mut extended_state: [MaybeUninit<u32>; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
            [const { MaybeUninit::uninit() }; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS];

        let state_base_addr = x10;
        for i in 0..BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS {
            let state_word_addr = state_base_addr + (core::mem::size_of::<u32>() * i) as u32;
            let value = ram.peek_word(state_word_addr);
            extended_state[i].write(value);
        }
        let mut extended_state = extended_state.map(|el| el.assume_init());

        // and input doesn't change across calls
        let mut input: [MaybeUninit<u32>; BLAKE2S_BLOCK_SIZE_U32_WORDS] =
            [const { MaybeUninit::uninit() }; BLAKE2S_BLOCK_SIZE_U32_WORDS];

        let input_base_addr = x11;
        for i in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
            let input_word_addr = input_base_addr + (core::mem::size_of::<u32>() * i) as u32;
            let value = ram.peek_word(input_word_addr);

            input[i].write(value);
        }
        let input = input.map(|el| el.assume_init());

        // for efficiency we can just run blake round function at once
        if reduced_rounds {
            blake2s_u32::round_function_reduced_rounds(&mut extended_state, &input);
        } else {
            blake2s_u32::round_function_full_rounds(&mut extended_state, &input);
        }

        // for g_function_call_idx in 0..num_invocations {
        //     let round_number =
        //         (g_function_call_idx as usize) / BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
        //     let mixing_function_number =
        //         (g_function_call_idx as usize) % BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
        //     let sigma_pairs = &SIGMAS_BY_PAIRS[round_number];

        //     let [a, b, c, d] = MIXING_FUNCTION_ACCESS_IDXES[mixing_function_number];
        //     let [x, y] = sigma_pairs[mixing_function_number];

        //     g_function(&mut extended_state, a, b, c, d, input[x], input[y]);

        //     // as we read all the input and touch all the state each round, we only need to
        //     // bookkeep as if at the last round, and we do it below
        // }

        // bookkeeping is done once - we dump all elements into the RAM log, and write to memory.
        // The only non-trivial element is to select write timestamps - we need those where
        // the corresponding state or input element was used the last time
        {
            // We do not care until the last round function, so we adjust our timestamp to the moment until we run
            // last 8 g-functions
            let last_round_ts_base = state.timestamp
                + (((_num_rounds - 1) * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION) as TimestampScalar)
                    * TIMESTAMP_STEP;
            let last_round_ts_base = last_round_ts_base | 3;
            let sigma_invs = if reduced_rounds {
                &REDUCED_ROUNDS_SIGMA_INV
            } else {
                &FULL_ROUNDS_SIGMA_INV
            };

            let base_addr = x10;
            let input_base_addr = x11;

            // we need an inverse mapping of state element index => g function index in the round function
            for idx in 0..BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS {
                let g_function_index = STATE_EL_INTO_MIXING_FUNCTION_ROUND[idx];
                let write_ts =
                    last_round_ts_base + (g_function_index as TimestampScalar) * TIMESTAMP_STEP;
                let value = extended_state[idx];
                let state_address = base_addr + ((idx * core::mem::size_of::<u32>()) as u32);
                let (ts, old_value) = ram.write_word(state_address, value, write_ts);
                snapshotter.append_memory_read(state_address, old_value, ts, write_ts);
            }

            for idx in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
                let g_function_index = sigma_invs[idx];
                let write_ts =
                    last_round_ts_base + (g_function_index as TimestampScalar) * TIMESTAMP_STEP;
                let input_addr = input_base_addr + ((idx * core::mem::size_of::<u32>()) as u32);
                let (ts, old_value) = ram.read_word(input_addr, write_ts);
                snapshotter.append_memory_read(input_addr, old_value, ts, write_ts);
            }
        }

        // and x12 is already updated
    }
    // and full machine state also moves!

    // But timestamp needs 1 less bump
    state.timestamp += ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP;
    state.counters.bump_blake2_g_function(num_invocations);
    E::on_delegation(
        state,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
        num_invocations as u64,
    );
    state.pc = state
        .pc
        .wrapping_add((core::mem::size_of::<u32>() * num_invocations) as u32);
    state
        .counters
        .log_multiple_circuit_family_calls::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
            num_invocations,
        );
}
