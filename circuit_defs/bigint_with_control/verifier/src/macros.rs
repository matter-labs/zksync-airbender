macro_rules! define_security_module {
    ($module:ident, $security_bits:expr) => {
        pub mod $module {
            use core::mem::MaybeUninit;

            use field::{
                batch_inverse_checked, Field, FieldExtension, Mersenne31Complex, Mersenne31Field,
                Mersenne31Quartic,
            };
            use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
            use verifier_common::cs::definitions::*;
            use verifier_common::fri_folding::fri_fold_by_log_n;
            use verifier_common::fri_folding::fri_fold_by_log_n_with_fma;
            use verifier_common::non_determinism_source::NonDeterminismSource;
            use verifier_common::prover::definitions::*;
            use verifier_common::structs::*;
            use verifier_common::transcript::Blake2sTranscript;
            use verifier_common::transcript_challenge_array_size;
            use verifier_common::DefaultLeafInclusionVerifier;
            use verifier_common::DefaultNonDeterminismSource;
            use verifier_common::ProofOutput;

            pub mod concrete {
                // Compile the verifier twice with identical geometry code and only
                // a different security schedule. The generated `concrete` module is
                // intentionally just wiring: all shared verifier logic stays in the
                // common `concrete/*.rs` and `shared/` files.
                pub const SECURITY_BITS: usize = $security_bits;

                // Note: these modules access `SECURITY_BITS` as `super::SECURITY_BITS`
                // so that we efficiently have a copy of `concrete/` for each
                // security profile.
                #[path = "../../concrete/layout_import.rs"]
                pub mod layout_import;
                #[path = "../../concrete/quotient_eval_import.rs"]
                pub(crate) mod quotient_eval_import;
                #[path = "../../concrete/size_constants.rs"]
                pub mod size_constants;
                #[path = "../../concrete/skeleton_instance.rs"]
                pub mod skeleton_instance;

                pub(crate) use self::layout_import::VERIFIER_COMPILED_LAYOUT;
                pub use self::quotient_eval_import::evaluate_quotient;
                pub(crate) use self::size_constants::*;
                pub(crate) use self::skeleton_instance::*;
            }
            use crate::ProofPublicInputs;

            #[path = "../shared/mod.rs"]
            mod shared;

            pub use self::shared::{
                verify, verify_with_configuration, ConcreteProofOutput, ConcreteProofPublicInputs,
            };
        }
    };
}

pub(crate) use define_security_module;
