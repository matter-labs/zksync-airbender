use super::*;

pub mod prover;
pub mod sumcheck;
pub mod whir;
pub mod witness_gen;

/// switchover point: if work_size < PAR_THRESHOLD then we use a single thread
const PAR_THRESHOLD: usize = 1 << 10;