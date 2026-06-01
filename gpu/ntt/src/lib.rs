//! GPU NTT subsystem: forward/inverse NTT kernels + twiddle device context.
//! Owns its own device-linked CUDA archive (native/ntt). Built on gpu_core.
//!
//! The `cuda_struct_and_stub!` device-symbol stubs for the twiddle tables in
//! `ntt_twiddles` are co-located here with their `__constant__` definitions in
//! `native/ntt`, so this crate device-links self-contained.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg_attr(test, feature(allocator_api))]

mod upstream;

pub mod ntt;
pub mod ntt_twiddles;
