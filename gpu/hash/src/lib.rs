//! GPU blake2s hashing primitives: leaf/node hashing, Merkle-tree construction,
//! oracle/path gathering (`gather`), and the Fiat-Shamir transcript
//! (`transcript`: commit/squeeze/PoW).
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers) and
//! `gpu_ops` (the size-generic `bit_reverse_in_place` used on digest leaves).
//! Owns its own device-linked CUDA archive (`native/`: `hash.cu`, `gather.cu`)
//! and exports `hash.cuh`'s include dir via `links = "gpu_hash_native"` so the
//! blake2s-dependent GKR/WHIR protocol kernels that stay in `circuit_prover`
//! (`ops::gkr_ops`) can `#include "hash.cuh"`.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

mod upstream;

pub mod blake2s;
