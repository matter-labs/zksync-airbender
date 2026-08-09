//! Standalone CUDA benchmark for one uniskip sumcheck pass (k = 4).
//!
//! The crate is self-contained: it generates a synthetic program with a
//! production-shaped census instead of consuming a real GKR layout, so it can be
//! iterated on without the prover stack. See `README.md`.

pub mod abi;
pub mod cache;
pub mod compact;
pub mod coset_cache;
pub mod domain;
pub mod geometry;
pub mod harness;
pub mod kernels;
pub mod pair;
pub mod reference;
pub mod synth;
pub mod window;

#[cfg(test)]
gpu_core::force_serial_libtest!();
