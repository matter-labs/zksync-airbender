pub use common_constants::*;

pub const NUM_REGISTERS: usize = 32;
pub const REGISTER_SIZE: usize = 2;
pub const REGISTER_BYTE_SIZE: usize = 4;

pub const MAX_NUMBER_OF_CYCLES: u64 = 1
    << ((NUM_TIMESTAMP_COLUMNS_FOR_RAM as u32) * TIMESTAMP_COLUMNS_NUM_BITS
        - NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);

pub const NUM_MEM_ARGUMENT_KEY_PARTS: usize =
    1 + REGISTER_SIZE + NUM_TIMESTAMP_COLUMNS_FOR_RAM + REGISTER_SIZE;
pub const NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES: usize = NUM_MEM_ARGUMENT_KEY_PARTS - 1;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX: usize = 0;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX: usize = 1;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX: usize = 2;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX: usize = 3;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX: usize = 4;
pub const MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX: usize = 5;

pub const NUM_DELEGATION_ARGUMENT_KEY_PARTS: usize = 1 + 1 + 2; // delegation type, abi mem high offset, and timestamp (low and high)
pub const NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES: usize =
    NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1;
pub const DELEGATION_ARGUMENT_CHALLENGED_IDX_ABI_MEM_OFFSET_HIGH: usize =
    NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES - 3;
pub const DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW: usize =
    NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES - 2;
pub const DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH: usize =
    NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES - 1;

pub const NUM_LOOKUP_ARGUMENT_KEY_PARTS: usize = 3 + 1;
pub const NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES: usize = NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1;

pub const NUM_ELEMENTS_FOR_EXTERNAL_VALUES: usize =
    4 * NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES + 4 + REGISTER_SIZE + REGISTER_SIZE;

pub const EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH: usize =
    2 + 1 + 1 + 1 + 1 + REGISTER_SIZE + 1 + 1;

pub const EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES: usize =
    EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH - 1;

pub const NUM_INTERMEDIATE_MACHINE_STATE_LINEARIZATION_CHALLENGES: usize =
    1 + NUM_TIMESTAMP_COLUMNS_FOR_RAM + EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH - 1;
pub const NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES: usize = NUM_TIMESTAMP_COLUMNS_FOR_RAM + 2 - 1; // TIMESTAMP and PC
pub const MACHINE_STATE_CHALLENGE_POWERS_PC_HIGH_IDX: usize = 0;
pub const MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX: usize = 1;
pub const MACHINE_STATE_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX: usize = 2;

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
