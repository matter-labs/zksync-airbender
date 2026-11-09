//! Upstream re-export manifest for `gpu_prover_context`.
//!
//! `context.rs` and `transfer.rs` consume only `gpu_core`, `gpu_ntt`, and the
//! `era_cudart*`/`log` crates directly — none of the upstream `cs`/`prover`/
//! `field`/`setups`/`trace_and_split` crates. The `#[cfg(test)]` entries are the
//! CPU oracle of the Proth120 context test (dev-dependencies); add entries
//! here (not direct `use`s) if a future change in this crate needs one.

#[cfg(test)]
pub(crate) use fft::{precompute_twiddles_for_fft, proth120_lazy::lde_coset_lazy_r8};
#[cfg(test)]
pub(crate) use field::Field;
#[cfg(test)]
pub(crate) use worker::Worker;
