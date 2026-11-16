//! GPU NTT subsystem: forward/inverse NTT kernels + twiddle device context,
//! for BabyBear (`baby_bear`) and Proth120 (`proth120`). Owns its own
//! device-linked CUDA archive (`native/`). Built on gpu_core.
//!
//! The `cuda_struct_and_stub!` device-symbol stubs for the twiddle tables in
//! `baby_bear::twiddles` are co-located here with their `__constant__`
//! definitions in `native/baby_bear`, so this crate device-links self-contained.

#![cfg_attr(test, feature(allocator_api))]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]

mod shared;
mod twiddles;
mod upstream;

pub mod baby_bear;
pub mod proth120;

#[cfg(test)]
gpu_core::force_serial_libtest!();
