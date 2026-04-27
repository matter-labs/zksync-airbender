use super::*;
use blake2s_u32::g_function_control_flags::*;
use common_constants::delegation_types::blake2s_g_function::*;

// NOTE: if the control is not meaningful, we will output values
// that will not allow to compose a round function
pub fn create_blake_g_function_control_and_offsets_table<F: PrimeField>(id: u32) -> LookupTable<F> {
    let mut keys = Vec::with_capacity(1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS);
    for control_with_exe in 0..1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS {
        let key = [F::from_u32_unchecked(control_with_exe)];
        keys.push(key);
    }
    let table_name = format!("Blake G-function control and offsets table");

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        1 + BLAKE2S_G_FUNCTION_X10_NUM_WRITES + BLAKE2S_G_FUNCTION_X11_NUM_READS,
        |keys| {
            let x12 = keys[0].as_u32_reduced();
            debug_assert!(x12 < (1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS));

            let control_bitmask = x12 >> BLAKE2S_G_FUNCTION_COUNTER_BITS;
            let counter = x12 & ((1 << BLAKE2S_G_FUNCTION_COUNTER_BITS) - 1);
            let reduced_rounds =
                control_bitmask & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;
            let num_rounds = if reduced_rounds { 7 } else { 10 };
            let max_counter = num_rounds * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
            let mut next_counter = counter + 1;
            if next_counter as usize >= max_counter {
                next_counter = 0;
            }

            let next_x12 = (control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS) | next_counter;

            let g_function_call_idx = if counter as usize >= max_counter {
                0
            } else {
                counter
            };
            let round_number =
                (g_function_call_idx as usize) / BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
            let mixing_function_number =
                (g_function_call_idx as usize) % BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;

            use blake2s_u32::SIGMAS_BY_PAIRS;
            use riscv_transpiler::vm::delegations::blake2_g_function::MIXING_FUNCTION_ACCESS_IDXES;

            let sigma_pairs = &SIGMAS_BY_PAIRS[round_number];
            let [a, b, c, d] = MIXING_FUNCTION_ACCESS_IDXES[mixing_function_number];
            let [x, y] = sigma_pairs[mixing_function_number];

            let mut result = ArrayVec::new();
            result.push(F::from_u32_with_reduction(next_x12));
            // and then indexes
            for el in [a, b, c, d] {
                result.push(F::from_u32_with_reduction(el as u32));
            }
            for el in [x, y] {
                result.push(F::from_u32_with_reduction(el as u32));
            }

            (x12 as usize, result)
        },
        Some(first_key_index_gen_fn::<F>),
        id,
    )
}
