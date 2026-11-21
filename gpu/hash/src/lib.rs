//! GPU blake2s hashing primitives: leaf/node hashing, Merkle-tree construction,
//! oracle/path gathering (`gather`), and the Fiat-Shamir transcript
//! (`transcript`: commit/squeeze/PoW).
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers).
//! Owns its own device-linked CUDA archive (`native/`: `hash.cu`, `gather.cu`)
//! and exports `hash.cuh`'s include dir via `links = "gpu_hash_native"` so the
//! blake2s-dependent GKR/WHIR protocol kernels in `gpu_gkr`/`gpu_whir`
//! (`gpu/gkr/native/ops/baby_bear/gkr_ops.cu`, `gpu/whir/native/baby_bear/leaves.cu`) can `#include "hash.cuh"`.

mod upstream;

pub mod blake2s;
pub mod keccak256;
pub mod pow;

#[cfg(test)]
gpu_core::force_serial_libtest!();
