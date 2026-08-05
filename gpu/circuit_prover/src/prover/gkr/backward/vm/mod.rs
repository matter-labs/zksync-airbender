//! Backward segmented VM runtime.
//!
//! The portable compiler emits separate R0 and continuation programs. This
//! module owns only GPU binding, descriptors, launch geometry, and the temporary
//! environment selector used by proof-parity runs.

pub(crate) mod coords;
pub(crate) mod production_bind;
pub(crate) mod production_program;
pub(crate) mod seg;
pub(crate) mod seg_coeff_eval;
pub(crate) mod seg_desc;
pub(crate) mod seg_lower;

#[cfg(test)]
mod seg_abi_tests;
