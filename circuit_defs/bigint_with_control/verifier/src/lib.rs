#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![feature(slice_from_ptr_range)]
#![cfg_attr(not(any(test, feature = "proof_utils")), feature(allocator_api))]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(feature = "proof_utils")]
extern crate alloc;

#[cfg(all(not(feature = "security_80"), not(feature = "security_100")))]
compile_error!("at least one security level must be selected");

mod macros;

use crate::macros::define_security_module;
pub use field;
pub use verifier_common;
pub use verifier_common::blake2s_u32;
pub use verifier_common::prover;
pub use verifier_common::structs::*;
pub use verifier_common::transcript;
pub use verifier_common::ProofPublicInputs;

#[cfg(feature = "security_100")]
define_security_module!(security_100, verifier_common::SECURITY_BITS_100);
#[cfg(feature = "security_80")]
define_security_module!(security_80, verifier_common::SECURITY_BITS_80);

#[cfg(feature = "security_100")]
pub use security_100::verify as verify_security_100;
#[cfg(feature = "security_80")]
pub use security_80::verify as verify_security_80;

// Keep the legacy single-security exports so existing callers do not need
// to change until they opt into compiling both variants at once.
#[cfg(all(feature = "security_100", not(feature = "security_80")))]
pub use security_100::{
    concrete, verify, verify_with_configuration, ConcreteProofOutput, ConcreteProofPublicInputs,
};
#[cfg(all(feature = "security_80", not(feature = "security_100")))]
pub use security_80::{
    concrete, verify, verify_with_configuration, ConcreteProofOutput, ConcreteProofPublicInputs,
};
