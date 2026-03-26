#![expect(warnings)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use ::prover::*;
use prover::field::*;

pub mod mersenne_wrapper;
pub use self::mersenne_wrapper::*;

pub mod gkr;
pub mod utils;
pub mod whir;

#[cfg(test)]
mod test {
    use std::io::Write;

    use super::*;

    fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
        let src = std::fs::File::open(filename).expect(&format!("{} doesn't exist", filename));
        serde_json::from_reader(src).unwrap()
    }

    fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
        let mut dst = std::fs::File::create(path).unwrap();
        dst.write_all(content.to_string().as_bytes()).unwrap();
        drop(dst);
        std::process::Command::new("rustfmt")
            .arg(path)
            .status()
            .ok();
    }

    #[test]
    fn generate_gkr_inlined() {
        use crate::mersenne_wrapper::DefaultBabyBearField;
        use prover::cs::gkr_compiler::GKRCircuitArtifact;
        use prover::field::baby_bear::base::BabyBearField;
        use prover::field::baby_bear::ext4::BabyBearExt4;
        use prover::gkr::prover::{GKRProof, WhirSchedule};
        use prover::merkle_trees::DefaultTreeConstructor;

        let circuit_names = vec!["add_sub_lui_auipc_mop", "jump_branch_slt", "shift_binop"];
        let whir_schedule = WhirSchedule::default_for_tests_80_bits();

        // Generate shared common/mod.rs by assembling fragments from each module
        let common_dir = "../verifier/src/generated/common";
        std::fs::create_dir_all(common_dir).unwrap();
        let common = {
            use crate::mersenne_wrapper::MersenneWrapper;
            let field_use_stmts = DefaultBabyBearField::field_use_statements();
            let field_struct = DefaultBabyBearField::field_struct();
            let quartic_struct = DefaultBabyBearField::quartic_struct();

            let transcript_fns =
                utils::transcript::generate_transcript_helpers::<DefaultBabyBearField>();
            let sumcheck_fns = utils::sumcheck::generate_sumcheck_helpers::<DefaultBabyBearField>();
            let gkr_fns = gkr::generate_gkr_common::<DefaultBabyBearField>();
            let whir_fns = whir::generate_whir_common::<DefaultBabyBearField>(&whir_schedule);

            quote::quote! {
                use core::mem::MaybeUninit;
                use ::verifier_common::field_ops;
                use ::verifier_common::field::{Field, FieldExtension, PrimeField};
                use ::verifier_common::blake2s_u32::{
                    AlignedArray64, DelegatedBlake2sState,
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                };
                use ::verifier_common::non_determinism_source::NonDeterminismSource;
                use ::verifier_common::transcript::{Blake2sTranscript, Seed};
                use ::verifier_common::gkr::{GKRVerificationError, LazyVec};
                #field_use_stmts

                pub const EXT_DEGREE: usize =
                    <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
                pub const DRAW_BUF_CAPACITY: usize = 64;

                #transcript_fns
                #sumcheck_fns
                #gkr_fns
                #whir_fns
            }
        };
        write_and_fmt(&format!("{}/mod.rs", common_dir), &common);

        for name in circuit_names {
            let compiled_circuit: GKRCircuitArtifact<BabyBearField> =
                deserialize_from_file(&format!(
                    "../cs/compiled_circuits/{}_preprocessed_layout_gkr.json",
                    name
                ));
            let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
                deserialize_from_file(&format!("../prover/test_proofs/{}_gkr_proof.json", name));

            let files = gkr::generate_gkr_inlined::<DefaultBabyBearField, _, _, _>(
                &compiled_circuit,
                &proof,
                4,
                &whir_schedule,
            );

            let dir = format!("../verifier/src/generated/{}", name);
            std::fs::create_dir_all(&dir).unwrap();

            let mod_rs = quote::quote! {
                pub mod constants;
                pub mod gkr;
                pub mod whir;
                #[path = "../common/mod.rs"]
                pub mod common;
                pub use gkr::verify_gkr_sumcheck;

                use ::verifier_common::non_determinism_source::NonDeterminismSource;
                use ::verifier_common::gkr::GKRVerificationError;

                #[derive(Clone, Debug)]
                pub enum VerificationError {
                    Gkr(GKRVerificationError),
                    Whir(common::WhirVerificationError),
                }

                /// Run the full GKR + WHIR verification pipeline.
                #[allow(unused_braces, unused_mut, unused_variables)]
                pub fn verify_all<I: NonDeterminismSource>() -> Result<(), VerificationError> {
                    let gkr_output = verify_gkr_sumcheck::<I>()
                        .map_err(VerificationError::Gkr)?;
                    let mut seed = gkr_output.whir_transcript_seed;
                    whir::verify_whir::<I>(
                        &mut seed,
                        gkr_output.whir_batching_challenge,
                        &gkr_output.setup_cap,
                        &gkr_output.memory_cap,
                        &gkr_output.witness_cap,
                    ).map_err(VerificationError::Whir)
                }
            };

            write_and_fmt(&format!("{}/mod.rs", dir), &mod_rs);
            write_and_fmt(&format!("{}/constants.rs", dir), &files.constants);
            write_and_fmt(&format!("{}/gkr.rs", dir), &files.gkr);

            let whir_initial = whir::generate_whir_inlined::<DefaultBabyBearField>(
                &whir_schedule,
                files.num_mem_oracle_cols,
                files.num_wit_oracle_cols,
                files.num_setup_oracle_cols,
                files.trace_len_log2,
            );
            let whir_internal = whir::generate_whir_internal_rounds::<DefaultBabyBearField>(
                &whir_schedule,
                files.trace_len_log2,
            );
            let whir_final = whir::generate_whir_final_round::<DefaultBabyBearField>(
                &whir_schedule,
                files.trace_len_log2,
            );
            let whir_verify = whir::generate_whir_verify::<DefaultBabyBearField>();
            let whir_code = quote::quote! {
                #whir_initial
                #whir_internal
                #whir_final
                #whir_verify
            };
            write_and_fmt(&format!("{}/whir.rs", dir), &whir_code);
        }
    }
}
