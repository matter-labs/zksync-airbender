#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg_attr(any(feature = "l1", all(test, feature = "verifiers")), feature(allocator_api))]

pub use ::prover;
pub use ::setups;

#[cfg(feature = "l1")]
pub mod l1;

mod recursion;
