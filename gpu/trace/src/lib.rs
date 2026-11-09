#![allow(incomplete_features)]
#![cfg_attr(test, feature(allocator_api))]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
#![allow(clippy::mut_from_ref)]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]

pub mod trace;
pub(crate) mod upstream;
pub mod witness;

#[cfg(test)]
gpu_core::force_serial_libtest!();
