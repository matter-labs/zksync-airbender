#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![feature(allocator_api)]
#![feature(slice_from_ptr_range)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(feature = "proof_utils")]
extern crate alloc;

pub use field;
pub use verifier_common;
pub use verifier_common::blake2s_u32;
pub use verifier_common::prover;
pub use verifier_common::transcript;

#[cfg(test)]
mod tests;
