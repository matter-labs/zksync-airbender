//! Upstream re-export manifest for `gpu_prover_context`.
//!
//! `context.rs` and `transfer.rs` consume only `gpu_core`, `gpu_ntt`, and the
//! `era_cudart*`/`log` crates directly — none of the upstream `cs`/`prover`/
//! `field`/`setups`/`trace_and_split` crates. Empty on purpose; add entries
//! here (not direct `use`s) if a future change in this crate needs one.
