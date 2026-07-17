//! Verifies the ported flatten/seed modules reproduce the known-good calldata and
//! seed bytes byte-for-byte from the on-disk circuit + proof + aux data.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

fn load_inputs() -> (GKRCircuitArtifact<Proth120>, Proof, CommitmentMode) {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open("../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json")
            .expect("circuit layout"),
    )
    .expect("deserialize circuit");
    let proof: Proof = serde_json::from_reader(
        std::fs::File::open("../prover/unified_circuit_proof_proth120.json").expect("proof"),
    )
    .expect("deserialize proof");
    let aux: CommitmentMode = serde_json::from_reader(
        std::fs::File::open("../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json")
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

    let handoff = verifier_evm::gkr_whir_handoff_seed(&proof);
    assert_eq!(
        hex::encode(handoff),
        read_fixture("gkr_whir_handoff_seed.hex"),
        "gkr_whir_handoff_seed diverged"
    );
    assert_eq!(
        hex::encode(handoff),
        "2b85b1e5ceedc1a3c4929323eed920ecabf439ef05b345377d776b82ad8cb1d9",
        "handoff seed diverged from the expected literal"
    );

    let gkr = verifier_evm::gkr_calldata(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(&gkr),
        read_fixture("gkr_full_calldata.hex"),
        "gkr_calldata diverged"
    );

    let whir = verifier_evm::whir_calldata(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(&whir),
        read_fixture("proth120_whir_calldata_from_proof.hex"),
        "whir_calldata diverged"
    );
}
