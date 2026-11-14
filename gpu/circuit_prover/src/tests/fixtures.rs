use super::*;
use prover::tests::gkr::orchestration::canonical_fixtures::CanonicalCircuit;

pub(super) struct CommittedProof {
    pub proof: GKRProof<BF, E4, DefaultTreeConstructor>,
    pub bytes: Vec<u8>,
}

pub(super) fn validate_committed_proof(
    circuit: CanonicalCircuit,
    config: &ProverConfig,
    proof: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(
        proof.whir_proof.whir_schedule, config.whir_schedule,
        "committed proof/config schedule mismatch"
    );
    let compiled = circuit.compiled_circuit(&test_artifact_path(""));
    let geometry = BaseCommitmentGeometry::from_config(config, BaseColumns::of(&compiled));
    assert_eq!(
        proof.whir_proof.memory_commitment.num_columns,
        geometry.oracle(BaseOracleRole::Memory).physical_columns(),
        "committed proof/circuit memory width mismatch"
    );
    assert_eq!(
        proof.whir_proof.witness_commitment.num_columns,
        geometry.oracle(BaseOracleRole::Witness).physical_columns(),
        "committed proof/circuit witness width mismatch"
    );
    assert_eq!(1 << config.trace_len_log2, compiled.trace_len);
}

pub(super) fn load_committed_proof(
    circuit: CanonicalCircuit,
    mode: circuit_common::SoundnessMode,
) -> CommittedProof {
    let root = test_artifact_path("");
    let bytes = std::fs::read(circuit.proof_path(&root, mode)).unwrap();
    let proof = proof_fixtures::decode(&bytes);
    validate_committed_proof(circuit, &circuit.prover_config(&root, mode), &proof);
    CommittedProof { proof, bytes }
}

#[test]
fn cpu_loads_complete_committed_proof_set() {
    use prover::tests::gkr::orchestration::canonical_fixtures::canonical_circuits;
    for &mode in circuit_common::SoundnessMode::ALL {
        for circuit in canonical_circuits(mode) {
            let loaded = load_committed_proof(circuit, mode);
            assert_eq!(
                proof_fixtures::encode(&loaded.proof, Vec::new()),
                loaded.bytes
            );
        }
    }
}

#[test]
#[should_panic(expected = "committed proof/config schedule mismatch")]
fn cpu_committed_proof_rejects_other_soundness_config() {
    let circuit = CanonicalCircuit::AddSubLuiAuipcMop;
    let loaded = load_committed_proof(circuit, circuit_common::SoundnessMode::DEFAULT);
    validate_committed_proof(
        circuit,
        &circuit.prover_config(
            &test_artifact_path(""),
            circuit_common::SoundnessMode::EthproofsSoundnessCalc,
        ),
        &loaded.proof,
    );
}

#[test]
#[should_panic(expected = "committed proof/circuit memory width mismatch")]
fn cpu_committed_proof_rejects_other_circuit() {
    let loaded = load_committed_proof(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::DEFAULT,
    );
    let other = CanonicalCircuit::ShiftBinop;
    validate_committed_proof(
        other,
        &other.prover_config(
            &test_artifact_path(""),
            circuit_common::SoundnessMode::DEFAULT,
        ),
        &loaded.proof,
    );
}
