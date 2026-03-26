#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(any(test, feature = "proof_utils"))]
extern crate alloc;

pub use field;
pub use verifier_common;
pub use verifier_common::blake2s_u32;
#[cfg(feature = "gkr_verify")]
pub use verifier_common::gkr;
pub use verifier_common::prover;
pub use verifier_common::transcript;

#[cfg(feature = "gkr_verify")]
#[path = "generated/add_sub_lui_auipc_mop/mod.rs"]
pub mod add_sub_lui_auipc_mop;

#[cfg(feature = "gkr_verify")]
#[path = "generated/jump_branch_slt/mod.rs"]
pub mod jump_branch_slt;

#[cfg(feature = "gkr_verify")]
#[path = "generated/shift_binop/mod.rs"]
pub mod shift_binop;
