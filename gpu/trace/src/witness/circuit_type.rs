//! Circuit identifiers and geometry now live in the CUDA-free
//! `execution_prover_model`, so a CPU backend can name them without linking
//! CUDA. This module re-exports them at their historical path.
pub use execution_prover_model::circuit_type::*;
