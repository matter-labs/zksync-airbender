#![cfg(all(feature = "host_utils", feature = "verifiers"))]

//! Proof fixtures must use the current schedule; a clean `git status` after
//! `tools/reproduce/reproduce.sh` ensures their standalone verifier guests also
//! match the generated code.

#[allow(dead_code)]
mod trace;

use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::prover::gkr::prover::GKRProof;
use verifier_common::prover::gkr::prover_config::example_configs::config_for_100_bits_under_pessimistic_conjecture;
use verifier_common::prover::merkle_trees::DefaultTreeConstructor;

const EXPECTED: &[(&str, u64)] = &[
    ("add_sub_lui_auipc_mop", 790694),
    ("jump_branch_slt", 818323),
    ("shift_binop", 832081),
    ("unsigned_mul_div", 771892),
    ("mem_word_only", 779215),
    ("mem_subword_only", 796003),
    ("inits_and_teardowns", 558648),
    ("blake2_with_extended_control", 2548929),
    ("bigint_with_extended_control", 1284974),
    ("keccak_special5", 1290262),
    ("blake2_g_function", 873065),
    ("keccak_column_parity", 1004556),
    ("keccak_theta_rho", 1111894),
    ("keccak_chi5", 1046954),
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

    // A stale proof and stale guest can agree with each other while both lag
    // behind the current prover. Check the fixture before executing the guest.
    let whir = &proof.whir_proof;
    assert!(whir.final_monomials.len().is_power_of_two());
    let trace_len_log2 = whir.whir_schedule.total_poly_size_reduction()
        + whir.final_monomials.len().ilog2() as usize;
    assert_eq!(
        whir.whir_schedule,
        config_for_100_bits_under_pessimistic_conjecture(trace_len_log2).whir_schedule,
        "{circuit}: stale proof fixture; regenerate the Sec100 proofs and per-circuit verifier binaries together"
    );

    let elf_path = format!("{root}/tools/gkr_verifier/{circuit}_sec_100.elf");
    assert!(
        std::path::Path::new(&elf_path).exists(),
        "open {elf_path}: no such file"
    );
    let (bin, text) =
        full_statement_verifier::host_utils::load_program(std::path::Path::new(&elf_path));

    let mut stream = Vec::new();
    proof.external_challenges.flatten_into_buffer(&mut stream);
    stream.extend(nds_for(circuit, &proof));

    trace::measure_verifier_cycles(&bin, &text, stream)
}

#[test]
fn per_circuit_verifier_cost_has_not_drifted() {
    for (circuit, expected) in EXPECTED {
        let actual = guest_cycles(circuit);
        let tolerance = expected / 1000;
        assert!(
            actual.abs_diff(*expected) <= tolerance,
            "{circuit}: {actual} vs expected {expected} (tolerance {tolerance}). The generated \
             verifier changed; recalibrate the cost tables. This guard is a proxy: the guest \
             runs only verify(), so it detects codegen drift but cannot validate the cost \
             table's numbers"
        );
    }
}

#[test]
#[ignore = "regenerate the Sec100 proof fixtures and verifier binaries (tools/reproduce/reproduce.sh) first"]
fn emit_per_circuit_verifier_costs() {
    for (circuit, _) in EXPECTED {
        println!("(\"{circuit}\", {}),", guest_cycles(circuit));
    }
}

#[test]
fn calibration_fixture_encoding_round_trips_every_compiled_circuit() {
    use full_statement_verifier::host_utils::fixture_codec;
    use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;

    let dir = format!("{}/cs/compiled_circuits", repo_root());
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if !path.to_string_lossy().ends_with("_layout_gkr.json") {
            continue;
        }
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let decoded: GKRCircuitArtifact<BabyBearField> =
            fixture_codec::decode(&fixture_codec::encode(&artifact, Vec::new()));
        assert!(
            decoded == artifact,
            "{} changed in the fixture encoding",
            path.display()
        );
        checked += 1;
    }
    assert!(checked > 0);
}
