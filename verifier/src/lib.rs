#![cfg_attr(not(any(test, feature = "proof_utils")), no_std)]

pub use field;
pub use verifier_common;
pub use verifier_common::blake2s_u32;
pub use verifier_common::gkr;
pub use verifier_common::prover;
pub use verifier_common::transcript;

#[path = "generated"]
mod __generated {
    macro_rules! declare_gkr_modules {
        ($($name:ident; $prod_path:expr),* $(,)?) => {
            $(
                pub mod $name {
                    pub mod sec_100;
                }
            )*
        };
    }
    verifier_common::gkr_circuits!(declare_gkr_modules);
}

pub use __generated::*;
