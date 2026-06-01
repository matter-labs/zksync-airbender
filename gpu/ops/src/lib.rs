//! GPU generic math/transform kernels: simple elementwise ops, powers,
//! squaring, transpose, bit-reversal, and batch inversion.
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers). Owns its
//! own device-linked CUDA archive (`native/`). `bit_reverse` is generic over
//! element *size*, so it carries no hashing/digest vocabulary; the blake2s
//! digest (`DG`) instantiation lives in `gpu_hash`, binding the 32-byte kernel
//! defined here via cross-crate link propagation.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

mod upstream;

pub mod bit_reverse;
pub mod powers;
pub mod simple;
pub mod squaring;
pub mod transpose;

// Test-support batch-inversion primitive. `#[doc(hidden)] pub` (not
// `#[cfg(test)]`) so `circuit_prover`'s own test suites can reach it across the
// crate boundary — a dependency's `#[cfg(test)]` items are invisible to
// consumers.
#[doc(hidden)]
pub mod batch_inv;
