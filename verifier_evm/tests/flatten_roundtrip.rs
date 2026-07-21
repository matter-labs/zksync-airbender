//! Verifies the ported flatten/seed modules reproduce the known-good calldata and
//! seed bytes byte-for-byte from the on-disk circuit + proof + aux data.

mod common;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

fn load_inputs() -> (GKRCircuitArtifact<Proth120>, Proof, CommitmentMode) {
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
    let aux: CommitmentMode = serde_json::from_reader(
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

    // The GKR→WHIR handoff seed is an intermediate value the prover records in the proof; the
    // flatten path surfaces it verbatim. The expectation is the proof file's own recorded value
    // (source of truth) — never a hardcoded literal that goes stale when the proof is regenerated.
    let handoff = verifier_evm::gkr_whir_handoff_seed(&proof);
    assert_eq!(
        Some(handoff),
        proof.intermediate_transcript_seed,
        "gkr_whir_handoff_seed diverged from the proof's recorded intermediate_transcript_seed"
    );

    let gkr = verifier_evm::gkr_calldata(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(&gkr),
        read_fixture("gkr_full_calldata.hex"),
        "gkr_calldata diverged"
    );

    let cfg = common::production_prover_config();
    let whir = verifier_evm::whir_calldata(
        &circuit,
        &proof,
        &aux,
        &cfg.whir_schedule.whir_steps_schedule,
        &cfg.whir_schedule.whir_queries_schedule,
    );
    assert_eq!(
        hex::encode(&whir),
        read_fixture("proth120_whir_calldata_from_proof.hex"),
        "whir_calldata diverged"
    );
}
