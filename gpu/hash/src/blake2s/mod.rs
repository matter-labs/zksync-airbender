//! Blake2s GPU subsystem, split by concern: `hash` (leaf hashing), `merkle`
//! (tree construction), `gather` (query leaf/path/cap gathering), `transcript`
//! (Fiat-Shamir commit/squeeze/PoW). Everything is re-exported flat here —
//! `blake2s::<item>` is the stable path downstream code uses.

use era_cudart::execution::CudaLaunchConfig;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::utils::{LOG_WARP_SIZE, WARP_SIZE};

mod gather;
mod gather_coset;
mod hash;
mod merkle;
mod transcript;

pub use gather::*;
pub use gather_coset::*;
pub use hash::*;
pub use merkle::*;
pub use transcript::*;

/// Blake2s state / digest width, in u32 words.
pub const STATE_SIZE: usize = 8;

/// A Blake2s digest (one Merkle tree node), as `STATE_SIZE` u32 words.
pub type Digest = [u32; STATE_SIZE];

// Path-gather launch geometry packs STATE_SIZE-word digests into warps.
const _: () = assert!(WARP_SIZE.is_multiple_of(STATE_SIZE as u32));

pub const MAX_PARTIAL_TREE_REDUCTION_LAYERS: u32 = 10;

const PARTIAL_PATH_BLOCK_MAX_THREADS: u32 = 256;

fn assert_reduction_layers(reduction_layers: u32) {
    assert!(
        (LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS).contains(&reduction_layers),
        "partial-tree reduction layers {reduction_layers} outside {LOG_WARP_SIZE}..={MAX_PARTIAL_TREE_REDUCTION_LAYERS}"
    );
}

fn partial_path_block_config(
    grid_dim: (u32, u32),
    reduction_layers: u32,
    stream: &CudaStream,
) -> CudaLaunchConfig<'_> {
    let threads = (1u32 << reduction_layers).min(PARTIAL_PATH_BLOCK_MAX_THREADS);
    let mut config = CudaLaunchConfig::basic(grid_dim, threads, stream);
    config.dynamic_smem_bytes = core::mem::size_of::<Digest>() << reduction_layers;
    config
}

/// Bounds-checked `usize` → `u32` narrowing for kernel launch parameters.
fn checked_u32(value: usize) -> u32 {
    assert!(value <= u32::MAX as usize);
    value as u32
}

#[cfg(test)]
mod tests;
