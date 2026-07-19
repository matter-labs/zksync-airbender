//! GPU NTT subsystem: forward/inverse NTT kernels + twiddle device context.
//! Owns its own device-linked CUDA archive (native/ntt). Built on gpu_core.
//!
//! The `cuda_struct_and_stub!` device-symbol stubs for the twiddle tables in
//! `ntt_twiddles` are co-located here with their `__constant__` definitions in
//! `native/ntt`, so this crate device-links self-contained.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg_attr(test, feature(allocator_api))]
// Launcher signatures mirror kernel parameter lists by design (same precedent
// as gpu_hash's crate-level allow): splitting them into config structs would
// obscure the 1:1 Rust<->kernel correspondence.
#![allow(clippy::too_many_arguments)]

mod upstream;

pub mod ntt;
pub mod ntt_twiddles;

#[cfg(feature = "bench")]
pub mod bench;

#[cfg(test)]
gpu_core::force_serial_libtest!();
