//! ONE-TIME migration: the existing `unified_circuit_proof_proth120.json` was serialized before
//! `GKRProof.intermediate_transcript_seed` existed (deserializes to `None`). This test
//! deserializes it, fills the field with the GKR→WHIR handoff seed (computed once via the
//! transcript replay), and reserializes it in place. After running once, the flatten/seed
//! functions read the seed straight from the proof instead of replaying.
//!
//! Run explicitly: `cargo test -p verifier_evm --test update_proof_seed -- --ignored`.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

const PROOF_PATH: &str = "../prover/unified_circuit_proof_proth120.json";

#[test]
#[ignore = "one-time migration; run explicitly with --ignored"]
fn populate_intermediate_transcript_seed() {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open("../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json")
            .unwrap(),
    )
    .unwrap();
    let mut proof: Proof =
        serde_json::from_reader(std::fs::File::open(PROOF_PATH).unwrap()).unwrap();
    let aux: CommitmentMode = serde_json::from_reader(
        std::fs::File::open("../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json")
            .unwrap(),
    )
    .unwrap();

    // Compute the full handoff state once via the transcript replay and stash the values into
    // the proof: the intermediate seed on GKRProof, and the batching / evaluation-point /
    // batched-opening on the WHIR sub-proof (all previously absent -> None in this older json).
    let hs = verifier_evm::seed::replay_handoff_state(&circuit, &proof, &aux);
    assert_eq!(
        hex::encode(hs.seed),
        "2b85b1e5ceedc1a3c4929323eed920ecabf439ef05b345377d776b82ad8cb1d9"
    );
    proof.intermediate_transcript_seed = Some(hs.seed);
    proof.whir_proof.batching_challenge = Some(hs.whir_batching);
    proof.whir_proof.original_evaluation_point = Some(hs.whir_point);
    proof.whir_proof.batched_opening = Some(hs.batched_opening);

    let json = serde_json::to_string_pretty(&proof).unwrap();
    std::fs::write(PROOF_PATH, json).unwrap();
    eprintln!(
        "wrote intermediate_transcript_seed + WHIR handoff fields into {PROOF_PATH} (pretty); seed = {}",
        hex::encode(hs.seed)
    );
}
