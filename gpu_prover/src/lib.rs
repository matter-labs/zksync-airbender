#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(btree_cursors)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(likely_unlikely)]
#![feature(once_cell_try)]
#![feature(pointer_is_aligned_to)]

pub(crate) mod allocator;
#[cfg(feature = "bench")]
pub mod bench;
pub(crate) mod execution;
pub(crate) mod ops;
pub(crate) mod primitives;
pub(crate) mod prover;
pub(crate) mod witness;

pub use execution::prover::{
    CommitMemoryResult, ExecutionKind, ExecutionProver, ExecutionProverConfiguration, ProveResult,
};
pub use primitives::machine_type;
pub use primitives::machine_type::MachineType;
