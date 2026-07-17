//! Blake2s GPU subsystem, split by concern: `hash` (leaf hashing), `merkle`
//! (tree construction), `gather` (query leaf/path/cap gathering), `transcript`
//! (Fiat-Shamir commit/squeeze/PoW). Everything is re-exported flat here —
//! `blake2s::<item>` is the stable path downstream code uses.

use gpu_core::primitives::utils::WARP_SIZE;

mod gather;
mod hash;
mod merkle;
mod transcript;

pub use gather::*;
pub use hash::*;
pub use merkle::*;
pub use transcript::*;

pub const STATE_SIZE: usize = 8;

pub type Digest = [u32; STATE_SIZE];

// Path-gather launch geometry packs STATE_SIZE-word digests into warps.
const _: () = assert!(WARP_SIZE % STATE_SIZE as u32 == 0);

/// Bounds-checked `usize` → `u32` narrowing for kernel launch parameters.
pub(crate) fn checked_u32(value: usize) -> u32 {
    assert!(value <= u32::MAX as usize);
    value as u32
}

#[cfg(test)]
mod tests;
