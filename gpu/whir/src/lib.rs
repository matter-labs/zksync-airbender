#![cfg_attr(test, feature(allocator_api))]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
#![allow(clippy::mut_from_ref)]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]

pub mod baby_bear;
pub mod pow;
pub mod proth120;
pub(crate) mod upstream;

pub(crate) fn whir_three_point_partials_len(half: usize) -> usize {
    const BLOCK_THREADS: usize = 256;
    if half <= BLOCK_THREADS {
        0
    } else {
        half.div_ceil(BLOCK_THREADS) * 3
    }
}

#[cfg(test)]
mod primitive_tests;
#[cfg(test)]
mod test_utils;

#[cfg(test)]
gpu_core::force_serial_libtest!();
