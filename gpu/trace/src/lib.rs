#![allow(incomplete_features)]
#![feature(allocator_api)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
#![allow(clippy::mut_from_ref)]
// The public trace/witness launchers mirror their CUDA kernels' parameter
// lists; splitting them into config structs would obscure the 1:1
// Rust<->kernel correspondence (same precedent as gpu_hash's / gpu_ntt's /
// gpu_execution_prover's crate-level allow).
#![allow(clippy::too_many_arguments)]

pub mod trace;
pub(crate) mod upstream;
pub mod witness;

#[cfg(test)]
gpu_core::force_serial_libtest!();
