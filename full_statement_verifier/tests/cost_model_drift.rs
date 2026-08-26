#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg(all(feature = "host_utils", feature = "verifiers"))]

#[allow(dead_code)]
mod trace;

use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::prover::gkr::prover::GKRProof;
use verifier_common::prover::merkle_trees::DefaultTreeConstructor;

const EXPECTED: &[(&str, u64)] = &[
    ("add_sub_lui_auipc_mop", 1031431),
    ("jump_branch_slt", 1057906),
    ("shift_binop", 1092174),
    ("unsigned_mul_div", 1053645),
    ("mem_word_only", 1017323),
    ("mem_subword_only", 1036422),
    ("inits_and_teardowns", 876826),
    ("blake2_with_extended_control", 2976533),
    ("bigint_with_extended_control", 1572641),
    ("keccak_special5", 1568920),
    ("blake2_g_function", 1068075),
];

fn repo_root() -> String {
    format!("{}/..", env!("CARGO_MANIFEST_DIR"))
}

fn nds_for(
    circuit: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) -> Vec<u32> {
    use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
    let path = format!(
        "{}/cs/compiled_circuits/{circuit}_layout_gkr.json",
        repo_root()
    );
    let f = std::fs::File::open(&path).unwrap_or_else(|e| panic!("open {path}: {e}"));
    let compiled: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_reader(std::io::BufReader::new(f)).expect("deserialize compiled circuit");
    verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(proof, &compiled)
}

fn guest_cycles(circuit: &str) -> u64 {
    let root = repo_root();
    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> = {
        let path = format!("{root}/prover/test_proofs/{circuit}_sec_100_gkr_proof.json");
        let f = std::fs::File::open(&path).unwrap_or_else(|e| panic!("open {path}: {e}"));
        serde_json::from_reader(std::io::BufReader::new(f)).expect("deserialize proof")
    };

    let bin_path = format!("{root}/tools/gkr_verifier/{circuit}_sec_100.bin");
    let text_path = format!("{root}/tools/gkr_verifier/{circuit}_sec_100.text");
    for path in [&bin_path, &text_path] {
        assert!(
            std::path::Path::new(path).exists(),
            "open {path}: no such file"
        );
    }
    let (bin, text) = full_statement_verifier::host_utils::load_program(
        std::path::Path::new(&bin_path),
        std::path::Path::new(&text_path),
    );

    let mut stream = Vec::new();
    proof.external_challenges.flatten_into_buffer(&mut stream);
    stream.extend(nds_for(circuit, &proof));

    trace::measure_verifier_cycles(&bin, &text, stream)
}

#[test]
fn per_circuit_verifier_cost_has_not_drifted() {
    for (circuit, expected) in EXPECTED {
        let actual = guest_cycles(circuit);
        assert_eq!(
            actual, *expected,
            "{circuit}: the generated verifier changed. Re-measure and update EXPECTED in this \
             file; regenerating the test proof, {circuit}_sec_100.bin/.text, or the compiled \
             circuit all move these counts. This guard is a proxy: the guest runs only verify(), \
             so it detects codegen drift but cannot validate the cost table's numbers"
        );
    }
}
