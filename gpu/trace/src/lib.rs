#![allow(incomplete_features)]
#![feature(allocator_api)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
#![allow(clippy::mut_from_ref)]

pub mod trace;
pub(crate) mod upstream;
pub mod witness;

#[cfg(test)]
gpu_core::force_serial_libtest!();
