use std::mem::MaybeUninit;

use super::*;
use blake2s_u32::g_function_control_flags::*;
use blake2s_u32::*;
use common_constants::*;

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

    assert!(x10 % 128 == 0, "state pointer is unaligned");
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

    // let round_number = (counter as usize) / BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
    // let mixing_function_number = (counter as usize) % BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;

    {
        let permutation_bitmask = x12 >> (16 + BLAKE2S_NUM_CONTROL_BITS);
        assert!(
            permutation_bitmask.is_power_of_two(),
            "permutation bitmask must be a bitmask, but got 0b{:b}",
            permutation_bitmask
        );
        let permutation_index = permutation_bitmask.trailing_zeros() as usize;
        assert_eq!(permutation_index, 0);
    }

    let num_rounds = if reduced_rounds { 7 } else { 10 };
    let num_mixing_function = num_rounds * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;

    let final_x12 = control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS;

    // let final_x12 = {
    //     let mut next_counter = (counter + 1) as usize;
    //     if next_counter == num_rounds * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION {
    //         next_counter = 0;
    //     }

    //     let final_x12 =
    //         (control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS) | (next_counter as u32);

    //     final_x12
    // };

    // we run full round function

    state.registers[10].timestamp =
        state.timestamp + ((num_mixing_function - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[11].timestamp =
        state.timestamp + ((num_mixing_function - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].timestamp =
        state.timestamp + ((num_mixing_function - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].value = final_x12;

    // NOTE: we should touch x0 and give it a timestamp that would be at the very end of execution
    state.registers[0].timestamp =
        (state.timestamp + ((num_mixing_function - 1) as TimestampScalar) * TIMESTAMP_STEP) | 2;

    unsafe {
        // read blake state, and input in full for speed, and for purposes of replayer it's also sufficient - replayer
        // can generate indexes of real accesses in the proper order (timestamps will be a little more painful, but not more than keccak)

        // NOTE: even though we use the same structure as full round function, we only need extended(!) state
        let mut extended_state: [MaybeUninit<u32>; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
            [const { MaybeUninit::uninit() }; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS];

        let mut addr =
            x10 + ((BLAKE2S_STATE_WIDTH_IN_U32_WORDS * core::mem::size_of::<u32>()) as u32);
        for i in 0..BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS {
            let value = ram.peek_word(addr);
            addr += core::mem::size_of::<u32>() as u32;

            extended_state[i].write(value);
        }
        let mut extended_state = extended_state.map(|el| el.assume_init());

        // and input doesn't change across calls
        let mut input: [MaybeUninit<u32>; 16] = [const { MaybeUninit::uninit() }; 16];

        let mut addr = x11;
        for i in 0..16 {
            let value = ram.peek_word(addr);
            addr += 4;

            input[i].write(value);
        }
        let input = input.map(|el| el.assume_init());

        for round in 0..num_mixing_function {
            let round_number = (round as usize) / BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
            let mixing_function_number = (round as usize) % BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
            let sigma_pairs = &SIGMAS_BY_PAIRS[round_number];

            const MIXING_FUNCTION_ACCESS_IDXES: [[usize; 4];
                BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION] = [
                [0, 4, 8, 12],
                [1, 5, 9, 13],
                [2, 6, 10, 14],
                [3, 7, 11, 15],
                [0, 5, 10, 15],
                [1, 6, 11, 12],
                [2, 7, 8, 13],
                [3, 4, 9, 14],
            ];

            let [a, b, c, d] = MIXING_FUNCTION_ACCESS_IDXES[mixing_function_number];
            let [x, y] = sigma_pairs[mixing_function_number];

            g_function(&mut extended_state, a, b, c, d, input[x], input[y]);

            let write_ts = state.timestamp + ((round - 1) as TimestampScalar) * TIMESTAMP_STEP;
            let write_ts = write_ts | 3;

            // TODO: rework to be more like keccak

            let base_addr =
                x10 + ((BLAKE2S_STATE_WIDTH_IN_U32_WORDS * core::mem::size_of::<u32>()) as u32);
            for idx in [a, b, c, d] {
                let value = extended_state[idx];
                let state_address = base_addr + ((idx * core::mem::size_of::<u32>()) as u32);
                let (ts, old_value) = ram.write_word(state_address, value, write_ts);
                snapshotter.append_memory_read(addr, old_value, ts, write_ts);
            }

            let base_addr = x11;
            for idx in [x, y] {
                let input_addr = base_addr + ((idx * core::mem::size_of::<u32>()) as u32);
                let (ts, old_value) = ram.read_word(input_addr, write_ts);
                snapshotter.append_memory_read(addr, old_value, ts, write_ts);
            }
        }

        // and x12 is already updated
    }
    // and full machine state also moves!

    // But timestamp needs 1 less bump
    state.timestamp += ((num_mixing_function - 1) as TimestampScalar) * TIMESTAMP_STEP;
    state
        .counters
        .bump_blake2_round_function(num_mixing_function);
    E::on_delegation(
        state,
        BLAKE2S_DELEGATION_CSR_REGISTER,
        num_mixing_function as u64,
    );
    state.pc = state
        .pc
        .wrapping_add((core::mem::size_of::<u32>() * num_mixing_function) as u32);
    state
        .counters
        .log_multiple_circuit_family_calls::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
            num_mixing_function,
        );
}
