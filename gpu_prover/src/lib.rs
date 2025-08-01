#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![feature(btree_cursors)]
#![feature(pointer_is_aligned_to)]
#![feature(new_zeroed_alloc)]
#![feature(vec_push_within_capacity)]
#![feature(iter_array_chunks)]
#![feature(iter_advance_by)]
#![feature(sync_unsafe_cell)]

pub mod allocator;
pub mod barycentric;
pub mod blake2s;
pub mod circuit_type;
pub mod device_context;
pub mod device_structures;
pub mod execution;
pub mod field;
pub mod field_bench;
pub mod ntt;
pub mod ops_complex;
pub mod ops_cub;
pub mod ops_simple;
pub mod prover;
pub mod utils;
pub mod witness;

pub use era_cudart as cudart;
pub use era_cudart_sys as cudart_sys;

#[cfg(test)]
mod tests;
