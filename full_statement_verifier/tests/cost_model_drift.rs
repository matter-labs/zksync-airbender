#![cfg(all(feature = "host_utils", feature = "verifiers"))]

//! Fixture codec round trip and a print-only per-circuit cycle diagnostic.
//! Census accuracy is checked on committed chains in `cost_model_trace`;
//! `build.sh` regenerates the guest-bound census tables.

#[allow(dead_code)]
mod trace;

use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::fsv_binaries::SoundnessMode;
use verifier_common::prover::gkr::prover::GKRProof;
use verifier_common::prover::merkle_trees::DefaultTreeConstructor;

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
    // the tracked per-circuit guests are the `blake2_with_compression` builds
    verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
        proof,
        &compiled,
        verifier_common::BlakeMode::Compression,
    )
}

fn guest_cycles(circuit: &str, mode: SoundnessMode) -> u64 {
    let circuit_data = verifier_common::test_circuits::CIRCUITS
        .iter()
        .find(|c| c.name == circuit)
        .unwrap_or_else(|| panic!("{circuit}: not a registered fixture circuit"));
    let level = verifier_common::test_circuits::SecurityLevel::Sec100;
    // The shared fixture loader rejects schedules that lag behind this mode's
    // current prover config, even if a stale proof and stale guest still agree.
    let proof = circuit_data.proof_for_mode(level, mode);

    let elf_path = circuit_data.elf_path_for_mode(level, mode);
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
#[ignore = "regenerate the Sec100 proof fixtures and verifier binaries (tools/reproduce/reproduce.sh) first"]
fn emit_per_circuit_verifier_costs() {
    for mode in [
        SoundnessMode::PessimisticConjecture,
        SoundnessMode::EthproofsSoundnessCalc,
    ] {
        println!("// {mode:?}");
        for circuit in verifier_common::test_circuits::CIRCUITS.iter() {
            let name = circuit.name;
            println!("(\"{name}\", {}),", guest_cycles(name, mode));
        }
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
