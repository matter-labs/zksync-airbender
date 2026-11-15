//! Verifies the ported flatten/seed modules reproduce the known-good calldata and
//! seed bytes byte-for-byte from the on-disk circuit + proof + aux data.

mod common;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

fn load_inputs() -> (GKRCircuitArtifact<Proth120>, Proof, OperationMode) {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .expect("circuit layout"),
    )
    .expect("deserialize circuit");
    let proof: Proof = serde_json::from_reader(
        std::fs::File::open("../prover/unified_circuit_proof_proth120.json").expect("proof"),
    )
    .expect("deserialize proof");
    let aux: OperationMode = serde_json::from_reader(
        std::fs::File::open(
            "../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json",
        )
        .expect("aux data"),
    )
    .expect("deserialize aux");
    (circuit, proof, aux)
}

fn read_fixture(name: &str) -> String {
    std::fs::read_to_string(format!("debug_data/{name}"))
        .unwrap_or_else(|_| panic!("read fixture {name}"))
        .trim()
        .to_string()
}

#[test]
fn flatten_and_seed_match_reference() {
    let (circuit, proof, aux) = load_inputs();

    let preimage = verifier_evm::commit_seed_preimage(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(&preimage),
        read_fixture("gkr_step1_preimage.hex"),
        "commit_seed_preimage diverged"
    );

    let gkr = verifier_evm::gkr_calldata(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(&gkr),
        read_fixture("gkr_full_calldata.hex"),
        "gkr_calldata diverged"
    );

    let cfg = common::production_prover_config();
    let merged = verifier_evm::merged_calldata(
        &circuit,
        &proof,
        &aux,
        &cfg.whir_schedule.fold_steps(),
        &cfg.whir_schedule.queries_per_round(),
    );
    assert_eq!(
        hex::encode(&merged),
        read_fixture("merged_calldata.hex"),
        "merged_calldata diverged"
    );
    // the single transaction's calldata is the GKR stream followed by the WHIR proof stream
    assert!(
        merged.starts_with(&gkr),
        "merged calldata must begin with the GKR stream"
    );

    // The registry mark: public/aux inputs are the final registers x10..x17 / x18..x25 (LE u32
    // each) — i.e. the preimage bytes at reg*12 — and the setup commitment hashes the setup cap.
    let mark = verifier_evm::verified_mark(&proof, &aux);
    let regs = |first: usize| -> Vec<u8> {
        (first..first + 8)
            .flat_map(|r| preimage[r * 12..r * 12 + 4].to_vec())
            .collect()
    };
    assert_eq!(
        mark.public_input.to_vec(),
        regs(10),
        "public_input != x10..x17"
    );
    assert_eq!(mark.aux_input.to_vec(), regs(18), "aux_input != x18..x25");
    assert_eq!(
        hex::encode(mark.to_bytes()),
        read_fixture("verified_mark.hex"),
        "verified_mark diverged"
    );
}
