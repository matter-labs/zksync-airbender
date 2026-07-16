//! GPU CUB-library wrappers: device-wide reduce, segmented reduce, radix sort,
//! and run-length encode.
//!
//! Built on `gpu_core` (allocator + primitives + base CUDA headers). Owns its
//! own device-linked CUDA archive (`native/`), isolating the compile-heavy CUB
//! (CCCL) template instantiations from the rest of the prover. Self-contained:
//! it launches only its own archive's kernels, so no header export is needed.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

mod upstream;

pub mod cub;
