#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(btree_cursors)]
#![feature(generic_const_exprs)]
#![feature(pointer_is_aligned_to)]

pub(crate) mod allocator;
pub(crate) mod ops;
pub mod primitives;
pub(crate) mod prover;
pub(crate) mod witness;

pub use primitives::circuit_type;
pub use primitives::device_context;
pub use primitives::device_structures;
pub use primitives::field;
pub use primitives::machine_type;
pub use primitives::utils;
