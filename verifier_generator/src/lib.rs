#![expect(warnings)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use ::prover::*;
use prover::field::*;

pub mod mersenne_wrapper;
pub use self::mersenne_wrapper::*;

pub mod gkr_inlining;

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

        for name in circuit_names {
            let compiled_circuit: GKRCircuitArtifact<BabyBearField> =
                deserialize_from_file(&format!(
                    "../cs/compiled_circuits/{}_preprocessed_layout_gkr.json",
                    name
                ));
            let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
                deserialize_from_file(&format!("../prover/test_proofs/{}_gkr_proof.json", name));

            let files = gkr_inlining::generate_gkr_inlined::<DefaultBabyBearField, _, _, _>(
                &compiled_circuit,
                &proof,
                4,
                &whir_schedule,
            );

            let dir = format!("../verifier/src/generated/{}", name);
            std::fs::create_dir_all(&dir).unwrap();

            write_and_fmt(&format!("{}/mod.rs", dir), &files.mod_rs);
            write_and_fmt(&format!("{}/constants.rs", dir), &files.constants);
            write_and_fmt(&format!("{}/gkr.rs", dir), &files.gkr);
            write_and_fmt(&format!("{}/whir.rs", dir), &files.whir);
            write_and_fmt(&format!("{}/merkle.rs", dir), &files.merkle);
        }
    }
}
