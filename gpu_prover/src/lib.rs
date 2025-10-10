#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(assert_matches)]
#![feature(btree_cursors)]
#![feature(extend_one_unchecked)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(iter_advance_by)]
#![feature(iter_array_chunks)]
#![feature(likely_unlikely)]
#![feature(once_cell_try)]
#![feature(pointer_is_aligned_to)]
#![feature(sync_unsafe_cell)]
#![feature(vec_push_within_capacity)]

pub mod allocator;
pub mod barycentric;
pub mod blake2s;
pub mod circuit_type;
pub mod device_context;
pub mod device_structures;
pub mod execution;
pub mod field;
pub mod field_bench;
pub mod machine_type;
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
pub(crate) mod tests;
