//! fwd-VM program acquisition (Task 1, host-only) for the A/B bench harness
//! over `gpu_gkr_compiler` fwd-VM `CompiledCircuit` programs.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))` (inherited from
//! `bench_interp`, see `bench_interp/mod.rs`). No production wiring. The
//! legacy v1 bench interpreter (`InterpDesc3`, `native/bench/gkr_fwd_vm.cu`)
//! is gone (Task 12) — the A/B report (`tests::fwd_vm_ab_report`) drives the
//! production v2 fwd-VM kernels (`super::super::vm`) directly.

pub(crate) mod compile;
pub(crate) mod report;
pub(crate) mod resolvers;
mod tests;
