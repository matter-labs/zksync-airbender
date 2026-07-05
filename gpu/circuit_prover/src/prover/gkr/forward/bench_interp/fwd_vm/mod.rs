//! fwd-VM program acquisition (Task 1, host-only) for the planned CUDA
//! interpreter over `gkr_eval_isa` fwd-VM `CompiledCircuit` programs.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))` (inherited from
//! `bench_interp`, see `bench_interp/mod.rs`). No production wiring.

pub(crate) mod compile;
pub(crate) mod lower;
pub(crate) mod resolvers;
mod tests;
