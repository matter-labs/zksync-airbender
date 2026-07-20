//! GPU generic math/transform kernels: simple elementwise ops, powers,
//! squaring, transpose, and bit-reversal.
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers). Owns its
//! own device-linked CUDA archive (`native/`). `bit_reverse` is generic over
//! element *size*, so it carries no hashing/digest vocabulary: any 32-byte POD
//! (e.g. `[u32; 8]`) reinterprets onto the same 32-byte kernel defined here, so
//! no per-type instantiation is needed.

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
