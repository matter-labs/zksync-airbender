//! GPU blake2s hashing primitives: leaf/node hashing, Merkle-tree construction,
//! oracle/path gathering (`gather`), and the Fiat-Shamir transcript
//! (`transcript`: commit/squeeze/PoW).
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers).
//! Owns its own device-linked CUDA archive (`native/`: `hash.cu`, `gather.cu`)
//! and exports `hash.cuh`'s include dir via `links = "gpu_hash_native"` so the
//! blake2s-dependent GKR/WHIR protocol kernels that stay in `gpu_circuit_prover`
//! (`ops/gkr_ops.cu`, `prover/whir/leaves.cu`) can `#include "hash.cuh"`.

// The public launchers mirror their CUDA kernels' parameter lists; splitting
// them into config structs would obscure the 1:1 Rust<->kernel correspondence.
#![allow(clippy::too_many_arguments)]

mod upstream;

pub mod blake2s;

#[cfg(test)]
gpu_core::force_serial_libtest!();
