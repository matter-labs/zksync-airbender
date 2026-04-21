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
#[path = "generated"]
mod __generated {
    macro_rules! declare_gkr_modules {
        ($($name:ident: $schedule:ident: $layout_suffix:expr),* $(,)?) => {
            $(pub mod $name;)*
        };
    }
    verifier_common::gkr_circuits!(declare_gkr_modules);
}
#[cfg(feature = "gkr_verify")]
pub use __generated::*;
