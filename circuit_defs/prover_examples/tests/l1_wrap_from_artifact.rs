#![cfg(feature = "l1")]

use full_statement_verifier::host_utils::build_unified_stream;
use full_statement_verifier::program_proof::ProgramProof;
use prover::tests::gkr::orchestration::common::ProgramConfig;
use prover::worker::Worker;
use std::path::PathBuf;

#[derive(serde::Deserialize)]
struct Checkpoint {
    proof: ProgramProof,
    setups: setups::Setups,
}

#[test]
#[ignore = "legacy Proth120 L1 wrap over an l1-feeder artifact from L1_FEEDER_ARTIFACT"]
fn legacy_l1_wrap_from_feeder_artifact() {
    let artifact = std::env::var("L1_FEEDER_ARTIFACT").expect("set L1_FEEDER_ARTIFACT");
    let out_dir = PathBuf::from(std::env::var("L1_WRAP_OUT_DIR").expect("set L1_WRAP_OUT_DIR"));
    let checkpoint: Checkpoint =
        serde_json::from_reader(std::fs::File::open(&artifact).expect("open artifact"))
            .expect("parse artifact");
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let stem = "fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension";
    let program = ProgramConfig {
        binary_path: root
            .join(format!("tools/gkr_verifier/{stem}.bin"))
            .to_string_lossy()
            .into_owned(),
        text_section_path: root
            .join(format!("tools/gkr_verifier/{stem}.text"))
            .to_string_lossy()
            .into_owned(),
        non_determinism_reads: build_unified_stream(&checkpoint.setups, &checkpoint.proof),
        cycles_bound: 1 << 22,
        ram_bound_bytes: 1 << 30,
    };
    let worker = match std::env::var("L1_WRAP_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
    {
        Some(n) => Worker::new_with_num_threads(n),
        None => Worker::new(),
    };
    prover_examples::l1::prove_l1_wrap_in_recompute_mode(
        &program,
        &root.join("cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"),
        &out_dir.join("unified_circuit_proof_proth120.json"),
        &out_dir.join("unified_circuit_proof_proth120_commitment_mod_aux_data.json"),
        &worker,
    );
}
