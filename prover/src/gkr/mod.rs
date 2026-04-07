use super::*;

pub mod prover;
pub mod sumcheck;
pub mod virtual_polys;
pub mod whir;
pub mod witness_gen;

/// Switchover point: if work_size < PAR_THRESHOLD then we use a single thread.
pub(crate) const PAR_THRESHOLD: usize = 1 << 10;

pub fn high_bits_offset_for_inits_and_teardowns<const WORD_BITS: u32>(trace_len: usize) -> u32 {
    assert!(WORD_BITS == 2 || WORD_BITS == 3);
    assert!(trace_len.trailing_zeros() + WORD_BITS >= 16);
    assert!(trace_len.is_power_of_two());
    trace_len.trailing_zeros() + WORD_BITS - 16
}
