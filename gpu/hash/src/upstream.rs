//! Upstream re-export manifest for `gpu_hash`.
//!
//! Production code is `gpu_core`/`gpu_ops`-only. The test suites verify the GPU
//! kernels against host references: the `field` trait and the host Fiat-Shamir
//! `transcript::Seed` (the standalone `transcript` crate — *not* `prover`).
//! Both are dev-only, so this shim is `#[cfg(test)]`.

#[cfg(test)]
pub(crate) use field::Field;
#[cfg(test)]
pub(crate) use transcript::Seed;
