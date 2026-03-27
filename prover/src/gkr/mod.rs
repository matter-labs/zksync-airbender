use super::*;

pub mod prover;
pub mod sumcheck;
pub mod virtual_polys;
pub mod whir;
pub mod witness_gen;

/// Switchover point: if work_size < PAR_THRESHOLD then we use a single thread.
pub(crate) const PAR_THRESHOLD: usize = 1 << 10;
