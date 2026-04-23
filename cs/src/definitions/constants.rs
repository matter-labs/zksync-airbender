pub use common_constants::*;

pub const NUM_REGISTERS: usize = 32;
pub const REGISTER_SIZE: usize = 2;
pub const REGISTER_BYTE_SIZE: usize = 4;

pub const MAX_NUMBER_OF_CYCLES: u64 = 1
    << ((NUM_TIMESTAMP_COLUMNS_FOR_RAM as u32) * TIMESTAMP_COLUMNS_NUM_BITS
        - NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);

pub const NUM_PERMUTATION_ARGUMENT_KEY_PARTS: usize =
    1 + REGISTER_SIZE + NUM_TIMESTAMP_COLUMNS_FOR_RAM + REGISTER_SIZE;
pub const NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES: usize =
    NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX: usize = 0;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX: usize = 1;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX: usize = 2;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX: usize = 3;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX: usize = 4;
pub const PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX: usize = 5;

pub const NUM_ELEMENTS_FOR_EXTERNAL_VALUES: usize =
    4 * NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 4 + REGISTER_SIZE + REGISTER_SIZE;

// pc + rs1/rs2/rd + imm + funct3 + mask
pub const EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH: usize =
    2 + 1 + 1 + 1 + REGISTER_SIZE + 1 + 1;

pub const MACHINE_STATE_CHALLENGE_POWERS_PC_LOW_IDX: usize =
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX; // PC is modeled as single memory cell, so PC value is value
pub const MACHINE_STATE_CHALLENGE_POWERS_PC_HIGH_IDX: usize =
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX;
pub const MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX: usize =
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX;
pub const MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX: usize =
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX;

pub const fn circuit_idx_and_row_into_timestamp(
    circuit_idx: u32,
    row: u32,
    trace_len_log_2: u32,
) -> TimestampScalar {
    let l = (row as TimestampScalar + 1) << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
    debug_assert!(l < (1 << trace_len_log_2));
    let h = (circuit_idx as TimestampScalar) << trace_len_log_2;
    h | l
}

pub const fn circuit_idx_and_row_into_timestamp_limbs(
    circuit_idx: u32,
    row: u32,
    trace_len_log_2: u32,
) -> [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
    let timestamp = circuit_idx_and_row_into_timestamp(circuit_idx, row, trace_len_log_2);
    let l = timestamp & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    let h = (timestamp >> TIMESTAMP_COLUMNS_NUM_BITS) as u32;

    [l as u32, h]
}

pub const fn row_into_timestamp_limbs_for_setup(row: u32) -> [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
    let timestamp = (row as TimestampScalar + 1) << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
    let l = timestamp & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    let h = (timestamp >> TIMESTAMP_COLUMNS_NUM_BITS) as u32;

    [l as u32, h]
}
