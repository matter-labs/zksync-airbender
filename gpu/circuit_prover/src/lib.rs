#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see primitives/context.rs.
#![allow(clippy::mut_from_ref)]

pub(crate) use gpu_core::allocator;
pub(crate) use gpu_core::primitives;
#[cfg(feature = "bench")]
pub mod bench;
pub(crate) mod ops;
// `prover` and `witness` are `pub` (not `pub(crate)`): `execution_prover` is
// carved into its own crate and drives the proving pipeline through these
// module paths. The proving entry points / host-transfer types it consumes are
// individually widened to `pub`; the rest of the trees stay `pub(crate)`.
pub mod prover;
#[allow(unused_imports)]
pub(crate) mod upstream;
pub mod witness;

pub use prover::config::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};
