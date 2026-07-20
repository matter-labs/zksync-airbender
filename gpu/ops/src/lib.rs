//! GPU generic math/transform kernels: simple elementwise ops, powers,
//! squaring, transpose, bit-reversal, and batch inversion.
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers). Owns its
//! own device-linked CUDA archive (`native/`). `bit_reverse` is generic over
//! element *size*, so it carries no hashing/digest vocabulary; the blake2s
//! digest (`Digest = [u32; 8]`) instantiation lives in `gpu_hash`, binding the 32-byte kernel
//! defined here via cross-crate link propagation.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

mod upstream;

pub mod bit_reverse;
pub mod powers;
pub mod simple;
pub mod squaring;
pub mod transpose;

#[cfg(test)]
gpu_core::force_serial_libtest!();
