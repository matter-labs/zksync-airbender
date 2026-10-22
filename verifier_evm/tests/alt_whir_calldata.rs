//! The merged tests' mismatched-halves control: the WHIR stream of ANOTHER valid wrap proof of
//! the version's shape. Its own target, so the `flatten_calldata` refresh
//! (`-- --ignored`) never needs the alternate proof.

mod common;

use sha3::{Digest, Keccak256};

#[test]
#[ignore = "writes the merged tests' alternate WHIR stream from AB_ALT_L1_PROOF / AB_ALT_L1_AUX"]
fn write_alt_whir_calldata() {
    let read = |var: &str| {
        let path = std::env::var(var).unwrap_or_else(|_| panic!("set {var}"));
        let bytes = std::fs::read(&path).unwrap_or_else(|_| panic!("read {path}"));
        (path, bytes)
    };
    let (proof_path, proof_bytes) = read("AB_ALT_L1_PROOF");
    let (_, aux_bytes) = read("AB_ALT_L1_AUX");
    for version in common::selected_versions() {
        let (circuit, proof, aux) = version.load();
        let alt_proof: common::Proof =
            serde_json::from_slice(&proof_bytes).expect("deserialize the alternate proof");
        let alt_aux: prover::gkr::prover::OperationMode =
            serde_json::from_slice(&aux_bytes).expect("deserialize the alternate aux");
        let prover::gkr::prover::OperationMode::SingleChunk { final_pc, .. } = alt_aux else {
            panic!("expected single-chunk operation mode");
        };
        let cfg = version.prover_config();
        let (folds, queries) = (
            &cfg.whir_schedule.whir_steps_schedule,
            &cfg.whir_schedule.whir_queries_schedule,
        );
        assert_eq!(
            alt_proof.whir_proof.whir_schedule, proof.whir_proof.whir_schedule,
            "the alternate proof has another WHIR schedule"
        );
        let whir = verifier_evm::whir_stream(&circuit, &proof, &aux, folds, queries);
        let alt = verifier_evm::whir_stream(&circuit, &alt_proof, &alt_aux, folds, queries);
        assert_eq!(
            alt.len(),
            whir.len(),
            "the alternate proof has another shape"
        );
        assert_ne!(alt, whir, "the alternate proof is the version's own proof");
        let path = version.contract_path("merged/testdata/alt_whir_stream.hex");
        std::fs::write(&path, hex::encode(&alt)).unwrap();
        eprintln!("wrote {} ({} bytes)", path.display(), alt.len());

        let readme = version.contract_path("merged/testdata/README.md");
        let text = std::fs::read_to_string(&readme).expect("testdata README");
        let current = text
            .lines()
            .position(|line| line.starts_with("Current file:"))
            .expect("README provenance line");
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        lines[current] = format!(
            "Current file: {} (keccak256 {}), final PC {final_pc}.",
            std::path::Path::new(&proof_path)
                .file_name()
                .unwrap()
                .to_string_lossy(),
            hex::encode(Keccak256::digest(&proof_bytes)),
        );
        std::fs::write(&readme, lines.join("\n") + "\n").unwrap();
        eprintln!("updated {}", readme.display());
    }
}
