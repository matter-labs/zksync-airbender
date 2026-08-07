//! Standalone CUDA benchmark for one uniskip sumcheck pass (k = 4).
//!
//! The crate is self-contained: it generates a synthetic program with a
//! production-shaped census instead of consuming a real GKR layout, so it can be
//! iterated on without the prover stack. See `README.md`.

pub mod domain;

#[cfg(test)]
gpu_core::force_serial_libtest!();
