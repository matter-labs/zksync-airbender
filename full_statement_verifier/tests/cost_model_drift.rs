#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg(all(feature = "host_utils", feature = "verifiers"))]

mod trace;

use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::prover::gkr::prover::GKRProof;
use verifier_common::prover::merkle_trees::DefaultTreeConstructor;

const EXPECTED: &[(&str, u64)] = &[
    ("add_sub_lui_auipc_mop", 837756),
    ("jump_branch_slt", 859309),
    ("shift_binop", 871029),
    ("unsigned_mul_div", 858290),
    ("mem_word_only", 825381),
    ("mem_subword_only", 841905),
    ("inits_and_teardowns", 697485),
    ("blake2_with_extended_control", 2364225),
    ("bigint_with_extended_control", 1276430),
    ("keccak_special5", 1258988),
    ("blake2_g_function", 850560),
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
        let path = format!("{root}/prover/test_proofs/{circuit}_sec_80_gkr_proof.json");
        let f = std::fs::File::open(&path).unwrap_or_else(|e| panic!("open {path}: {e}"));
        serde_json::from_reader(std::io::BufReader::new(f)).expect("deserialize proof")
    };

    let (bin, text) = full_statement_verifier::host_utils::load_program(
        std::path::Path::new(&format!("{root}/tools/gkr_verifier/{circuit}_sec_80.bin")),
        std::path::Path::new(&format!("{root}/tools/gkr_verifier/{circuit}_sec_80.text")),
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
        let tol = expected / 1000;
        assert!(
            actual.abs_diff(*expected) <= tol,
            "{circuit}: {actual} vs expected {expected} (tolerance {tol}) — \
             the generated verifier changed; recalibrate the cost tables. \
             This guard is a proxy: the guest runs only verify(), so it detects \
             codegen drift but cannot validate the cost table's numbers"
        );
    }
}
