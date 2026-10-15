use era_cudart::slice::DeviceSlice;

mod gather;
mod hash;
mod merkle;
mod transcript;

pub use gather::*;
pub use hash::*;
pub use merkle::*;
pub use transcript::*;

pub const DIGEST_WORDS: usize = 8;
pub const SEED_BYTES: usize = 32;
pub type Digest = [u32; DIGEST_WORDS];
pub type Seed = [u8; SEED_BYTES];

const _: () = {
    assert!(core::mem::size_of::<Digest>() == 32);
    assert!(core::mem::align_of::<Digest>() == 4);
    assert!(core::mem::size_of::<Seed>() == 32);
    assert!(core::mem::align_of::<Seed>() == 1);
};

fn checked_product(name: &str, left: usize, right: usize) -> usize {
    left.checked_mul(right)
        .unwrap_or_else(|| panic!("keccak256::{name}: count overflow"))
}

fn checked_bytes<T>(name: &str, count: usize) -> usize {
    checked_product(name, count, core::mem::size_of::<T>())
}

fn checked_log_size(name: &str, log: u32) -> usize {
    assert!(log <= 31, "keccak256::{name}: log_domain <= 31");
    1usize << log
}

fn checked_u32(name: &str, value: usize) -> u32 {
    u32::try_from(value).unwrap_or_else(|_| panic!("keccak256::{name}: u32 count overflow"))
}

fn checked_u64(name: &str, value: usize) -> u64 {
    u64::try_from(value).unwrap_or_else(|_| panic!("keccak256::{name}: u64 count overflow"))
}

fn tile_extent(name: &str, cosets: u32, stride: usize, extent: usize) -> usize {
    assert!(cosets >= 1, "keccak256::{name}: cosets_in_tile >= 1");
    assert!(stride >= extent, "keccak256::{name}: stride >= extent");
    checked_product(name, (cosets - 1) as usize, stride)
        .checked_add(extent)
        .unwrap_or_else(|| panic!("keccak256::{name}: tile extent overflow"))
}

const BLOCK_THREADS: u32 = 128;

fn grid_dim(name: &str, threads: usize, block_threads: u32) -> u32 {
    let blocks = threads.div_ceil(block_threads as usize);
    assert!(
        blocks <= i32::MAX as usize,
        "keccak256::{name}: grid <= 2^31 - 1"
    );
    blocks as u32
}

fn assert_no_overlap<T, U>(name: &str, left: &DeviceSlice<T>, right: &DeviceSlice<U>) {
    let left_bytes = checked_bytes::<T>(name, left.len());
    let right_bytes = checked_bytes::<U>(name, right.len());
    if left_bytes == 0 || right_bytes == 0 {
        return;
    }
    let left_start = left.as_ptr() as usize;
    let right_start = right.as_ptr() as usize;
    let left_end = left_start
        .checked_add(left_bytes)
        .unwrap_or_else(|| panic!("keccak256::{name}: pointer extent overflow"));
    let right_end = right_start
        .checked_add(right_bytes)
        .unwrap_or_else(|| panic!("keccak256::{name}: pointer extent overflow"));
    assert!(
        left_end <= right_start || right_end <= left_start,
        "keccak256::{name}: buffers must not overlap"
    );
}

#[cfg(test)]
mod tests;
