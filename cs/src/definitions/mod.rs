// this is defitnion of table types for purposes of doing no-std only for verifier
use ::field::PrimeField;

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;

mod constants;
mod constraints;
mod cycle_state;
mod decoding_utils;
mod gkr_layers;
mod lookup;
mod table_type;
mod unrolled_families;

pub mod gkr;

pub use self::constants::*;
pub use self::constraints::*;
pub use self::cycle_state::*;
pub use self::decoding_utils::*;
pub use self::gkr_layers::*;
pub use self::lookup::*;
pub use self::table_type::*;
pub use self::unrolled_families::*;

#[inline]
pub const fn timestamp_from_absolute_cycle_index(
    cycle_counter: usize,
    chunk_capacity: usize,
) -> TimestampScalar {
    let trace_len = chunk_capacity + 1;
    debug_assert!(trace_len.is_power_of_two());

    let chunk_index = cycle_counter / chunk_capacity;
    let index_in_chunk = cycle_counter % chunk_capacity;

    timestamp_from_chunk_cycle_and_sequence(index_in_chunk, chunk_capacity, chunk_index)
}

#[inline]
pub const fn timestamp_from_chunk_cycle_and_sequence(
    cycle_in_chunk: usize,
    chunk_capacity: usize,
    circuit_sequence: usize,
) -> TimestampScalar {
    let trace_len = chunk_capacity + 1;
    debug_assert!(trace_len.is_power_of_two());
    debug_assert!(cycle_in_chunk < trace_len);

    let timestamp = INITIAL_TIMESTAMP_AT_CHUNK_START
        + TIMESTAMP_STEP * (cycle_in_chunk as TimestampScalar)
        + timestamp_high_contribution_from_circuit_sequence(circuit_sequence, trace_len);

    timestamp
}

#[inline]
pub const fn timestamp_high_contribution_from_circuit_sequence(
    circuit_sequence: usize,
    trace_len: usize,
) -> TimestampScalar {
    debug_assert!(trace_len.is_power_of_two());
    // low timestamp chunk comes from the setup's two columns
    let timestamp_high_from_circuit_sequence = (circuit_sequence as TimestampScalar)
        << (trace_len.trailing_zeros() + NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);

    timestamp_high_from_circuit_sequence
}

pub const fn timestamp_scalar_into_column_values(
    timestamp: TimestampScalar,
) -> [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
    let low = timestamp & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    let high = timestamp >> TIMESTAMP_COLUMNS_NUM_BITS;

    [low as u32, high as u32]
}

pub fn split_timestamp(timestamp: TimestampScalar) -> (u32, u32) {
    let [low, high] = timestamp_scalar_into_column_values(timestamp);

    (low, high)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Variable(pub u64);

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Variable {
    pub const fn placeholder_variable() -> Self {
        Self(u64::MAX)
    }

    pub const fn is_placeholder(&self) -> bool {
        self.0 == u64::MAX
    }
}
