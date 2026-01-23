#![feature(allocator_api)]
#![feature(pointer_is_aligned_to)]
#![feature(btree_cursors)]

pub(crate) mod allocator;
pub(crate) mod circuit_type;
pub(crate) mod device_context;
pub(crate) mod device_structures;
pub mod field;
pub(crate) mod machine_type;
pub(crate) mod ops;
pub(crate) mod prover;
pub(crate) mod utils;
pub(crate) mod witness;

#[cfg(test)]
mod tests;
