//! Regenerates the verifier calldata + intermediate commit seed into `debug_data/` using the
//! production flatten/seed functions (from a serialized proof + aux + circuit). This is what a
//! deployment tool would call to prepare the two on-chain transactions' calldata. The two-tx
//! Foundry test reads these `debug_data/*.hex` files. Nothing here is read by `src/`.

mod common;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

fn load() -> (GKRCircuitArtifact<Proth120>, Proof, CommitmentMode) {
    let circuit = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .expect("circuit"),
    )
    .expect("deserialize circuit");
    let proof = serde_json::from_reader(
        std::fs::File::open("../prover/unified_circuit_proof_proth120.json").expect("proof"),
    )
    .expect("deserialize proof");
    let aux = serde_json::from_reader(
        std::fs::File::open(
            "../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json",
        )
        .expect("aux"),
    )
    .expect("deserialize aux");
    (circuit, proof, aux)
}

#[test]
fn write_calldata_into_debug_data() {
    let (circuit, proof, aux) = load();
    std::fs::create_dir_all("debug_data").unwrap();
    let put = |name: &str, bytes: &[u8]| {
        std::fs::write(format!("debug_data/{name}"), hex::encode(bytes)).unwrap();
        eprintln!("wrote debug_data/{name} ({} bytes)", bytes.len());
    };

    let cfg = common::production_prover_config();
    let (folds, queries) = (
        &cfg.whir_schedule.whir_steps_schedule,
        &cfg.whir_schedule.whir_queries_schedule,
    );
    put(
        "gkr_full_calldata.hex",
        &verifier_evm::gkr_calldata(&circuit, &proof, &aux),
    );
    put(
        "proth120_whir_calldata_from_proof.hex",
        &verifier_evm::whir_calldata(&circuit, &proof, &aux, folds, queries),
    );
    put(
        "gkr_step1_preimage.hex",
        &verifier_evm::commit_seed_preimage(&circuit, &proof, &aux),
    );
    put(
        "gkr_whir_handoff_seed.hex",
        &verifier_evm::gkr_whir_handoff_seed(&proof),
    );
}
