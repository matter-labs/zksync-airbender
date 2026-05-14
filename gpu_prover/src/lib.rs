#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(btree_cursors)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(likely_unlikely)]
#![feature(once_cell_try)]
#![feature(pointer_is_aligned_to)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see primitives/context.rs.
#![allow(clippy::mut_from_ref)]

pub(crate) mod allocator;
#[cfg(feature = "bench")]
pub mod bench;
pub(crate) mod execution;
pub(crate) mod ops;
pub(crate) mod primitives;
pub(crate) mod prover;
#[allow(unused_imports)]
pub(crate) mod upstream;
pub(crate) mod witness;

pub use execution::prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ExecutionProver, ExecutionProverConfiguration,
    ProveResult,
};
pub use primitives::machine_type;
pub use primitives::machine_type::MachineType;
