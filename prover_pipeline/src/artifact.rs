use super::{
    BlakeMode, L1Bundle, ProofCounts, ProofTarget, ProofTimingsMs, ProverBackend, SecurityLevel,
    SoundnessMode,
};
use full_statement_verifier::program_proof::ProgramProof;
use serde::{Deserialize, Serialize};
use setups::Setups;

/// The written schema: v4 plus the L1 fields (`feeder_layers`, `l1`).
pub const ARTIFACT_SCHEMA_VERSION: u32 = 6;
/// Legacy pessimistic artifacts, before the mode was recorded.
const LEGACY_SCHEMA_VERSION: u32 = 3;
/// Mode-explicit artifacts without the L1 fields; decoded, never written.
const MODE_SCHEMA_VERSION: u32 = 4;
/// The pre-rebase L1 layout. Never reused: rejected by number.
const PRE_REBASE_L1_SCHEMA_VERSION: u32 = 5;
const PRE_REBASE_L1_ERROR: &str =
    "UnsupportedArtifactVersion: 5: pre-rebase L1 artifact; unsupported; regenerate";

fn default_blake_tag() -> String {
    BlakeMode::Compression.tag().to_owned()
}

/// JSON proof artifact, schema v6; v4 decodes without the L1 fields and v3 explicitly as
/// legacy pessimistic. `proof` + `setups` are enough to
/// verify natively; `chain_end_params` is the ordered list of layer
/// `end_params` from base onward, from which the recursion chain state after
/// this artifact's layer (`chain_hash` / `chain_preimage`) is reconstructed
/// for staged continuation.
#[derive(Clone, Debug, Serialize)]
pub struct ProofArtifact {
    pub schema_version: u32,
    pub security_level: SecurityLevel,
    pub soundness_mode: SoundnessMode,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    pub cycles: u64,
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    pub program_cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final,
    /// feeder_1, .., feeder_k]`, one entry per proven layer.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Number of L1 feeder layers in `chain_end_params` (0 before the feeder
    /// stage, `1..=MAX_FEEDER_LAYERS` after it). Validated routing metadata:
    /// consecutive feeder layers prove the same binary on the same machine,
    /// so their end params are equal and the VM-authenticated chain hash
    /// (which deduplicates equal consecutive entries) cannot attest this
    /// count; verification rejects an isolated length mismatch only.
    pub feeder_layers: u32,
    /// Recursion-chain state AFTER this artifact's layer.
    pub chain_hash: [u32; 8],
    pub chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    pub blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    pub blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    pub blake_final: String,
    pub l1: Option<L1Bundle>,
    pub proof: ProgramProof,
    pub setups: Setups,
}

#[derive(Deserialize)]
struct ProofArtifactWire {
    #[serde(deserialize_with = "deserialize_artifact_version")]
    schema_version: u32,
    security_level: SecurityLevel,
    soundness_mode: Option<SoundnessMode>,
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    cycles: u64,
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    program_cycles: u64,
    program_bin_keccak: [u8; 32],
    program_text_keccak: [u8; 32],
    timings_ms: ProofTimingsMs,
    proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final, feeder_1, ..]`.
    chain_end_params: Vec<[u32; 8]>,
    /// v6 only; a v3/v4 artifact may carry only the neutral 0.
    feeder_layers: Option<u32>,
    /// Recursion-chain state AFTER this artifact's layer.
    chain_hash: [u32; 8],
    chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    blake_final: String,
    /// v6 only; a v3/v4 artifact may carry only the neutral null. Decoded in place:
    /// Proth120 values exceed what a buffered `serde_json::Value` keeps exactly.
    l1: Option<L1Bundle>,
    proof: ProgramProof,
    setups: Setups,
}

fn deserialize_artifact_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version == PRE_REBASE_L1_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(PRE_REBASE_L1_ERROR));
    }
    if version != LEGACY_SCHEMA_VERSION
        && version != MODE_SCHEMA_VERSION
        && version != ARTIFACT_SCHEMA_VERSION
    {
        return Err(<D::Error as serde::de::Error>::custom(format!("UnsupportedArtifactVersion: {version}; supported versions are 3 (legacy pessimistic), 4 and 6")));
    }
    Ok(version)
}

impl<'de> Deserialize<'de> for ProofArtifact {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = ProofArtifactWire::deserialize(deserializer)?;
        let mode = match (wire.schema_version, wire.soundness_mode) {
            (3, None | Some(SoundnessMode::PessimisticConjecture)) => {
                SoundnessMode::PessimisticConjecture
            }
            (3, Some(_)) => {
                return Err(<D::Error as serde::de::Error>::custom(
                    "ConflictingLegacySoundnessMode: schema v3 is legacy pessimistic",
                ))
            }
            (MODE_SCHEMA_VERSION | ARTIFACT_SCHEMA_VERSION, Some(mode)) => mode,
            (ARTIFACT_SCHEMA_VERSION, None) => {
                return Err(<D::Error as serde::de::Error>::custom(
                    "MissingSoundnessMode: schema v6 requires soundness_mode",
                ))
            }
            (_, None) => {
                return Err(<D::Error as serde::de::Error>::custom(
                    "MissingSoundnessMode: schema v4 requires soundness_mode",
                ))
            }
            (version, _) => {
                return Err(<D::Error as serde::de::Error>::custom(format!(
                    "UnsupportedArtifactVersion: {version}"
                )))
            }
        };
        let (feeder_layers, l1) = if wire.schema_version == ARTIFACT_SCHEMA_VERSION {
            let feeder_layers = wire.feeder_layers.ok_or_else(|| {
                <D::Error as serde::de::Error>::custom(
                    "MissingFeederLayers: schema v6 requires feeder_layers",
                )
            })?;
            (feeder_layers, wire.l1)
        } else {
            reject_legacy_l1_target(wire.schema_version, wire.target)
                .and_then(|()| {
                    reject_legacy_l1_fields(
                        wire.schema_version,
                        wire.feeder_layers.unwrap_or(0) != 0 || wire.l1.is_some(),
                    )
                })
                .map_err(<D::Error as serde::de::Error>::custom)?;
            (0, None)
        };
        Ok(Self {
            schema_version: wire.schema_version,
            security_level: wire.security_level,
            soundness_mode: mode,
            target: wire.target,
            backend: wire.backend,
            batch_id: wire.batch_id,
            cycles: wire.cycles,
            program_cycles: wire.program_cycles,
            program_bin_keccak: wire.program_bin_keccak,
            program_text_keccak: wire.program_text_keccak,
            timings_ms: wire.timings_ms,
            proof_counts: wire.proof_counts,
            chain_end_params: wire.chain_end_params,
            feeder_layers,
            chain_hash: wire.chain_hash,
            chain_preimage: wire.chain_preimage,
            blake_unrolled: wire.blake_unrolled,
            blake_bridge: wire.blake_bridge,
            blake_final: wire.blake_final,
            l1,
            proof: wire.proof,
            setups: wire.setups,
        })
    }
}
/// The L1 targets exist only from schema v6 on; an older artifact naming one is not a
/// legacy decode but a forged or misversioned L1 artifact.
fn reject_legacy_l1_target(version: u32, target: ProofTarget) -> Result<(), String> {
    if target >= ProofTarget::L1Feeder {
        return Err(format!(
            "UnsupportedArtifactTarget: schema v{version} cannot carry the L1 target {target:?}; L1 artifacts are schema v{ARTIFACT_SCHEMA_VERSION}"
        ));
    }
    Ok(())
}

fn reject_legacy_l1_fields(version: u32, present: bool) -> Result<(), String> {
    if present {
        return Err(format!(
            "UnsupportedArtifactField: schema v{version} has no L1 fields; L1 artifacts are schema v{ARTIFACT_SCHEMA_VERSION}"
        ));
    }
    Ok(())
}

impl ProofArtifact {
    pub(crate) fn validate_schema(&self) -> Result<(), String> {
        match self.schema_version {
            LEGACY_SCHEMA_VERSION
                if self.soundness_mode != SoundnessMode::PessimisticConjecture =>
            {
                return Err(
                    "ConflictingLegacySoundnessMode: schema v3 is legacy pessimistic".to_owned(),
                )
            }
            LEGACY_SCHEMA_VERSION | MODE_SCHEMA_VERSION => {
                reject_legacy_l1_target(self.schema_version, self.target)?;
                reject_legacy_l1_fields(
                    self.schema_version,
                    self.feeder_layers != 0 || self.l1.is_some(),
                )?;
            }
            ARTIFACT_SCHEMA_VERSION => {}
            PRE_REBASE_L1_SCHEMA_VERSION => return Err(PRE_REBASE_L1_ERROR.to_owned()),
            version => {
                return Err(format!(
                    "UnsupportedArtifactVersion: {version}; supported versions are 3, 4 and 6"
                ))
            }
        }
        Ok(())
    }

    /// Validate the caller's acceptance policy before source loading or backend work.
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        self.validate_schema()?;
        if self.soundness_mode != expected {
            return Err(format!(
                "SoundnessModeMismatch: expected {expected:?}, artifact is {:?}",
                self.soundness_mode
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn artifact(mode: SoundnessMode) -> ProofArtifact {
        ProofArtifact {
            schema_version: ARTIFACT_SCHEMA_VERSION,
            security_level: SecurityLevel::Sec100,
            soundness_mode: mode,
            target: ProofTarget::Base,
            backend: ProverBackend::Cpu,
            batch_id: 0,
            cycles: 0,
            program_cycles: 0,
            program_bin_keccak: [0; 32],
            program_text_keccak: [0; 32],
            timings_ms: ProofTimingsMs::default(),
            proof_counts: ProofCounts::default(),
            chain_end_params: vec![[0; 8]],
            feeder_layers: 0,
            chain_hash: [0; 8],
            chain_preimage: [0; 16],
            blake_unrolled: default_blake_tag(),
            blake_bridge: default_blake_tag(),
            blake_final: default_blake_tag(),
            l1: None,
            proof: ProgramProof {
                riscv_proofs: Default::default(),
                compiled_riscv_circuits: Default::default(),
                inits_and_teardown_proofs: Vec::new(),
                inits_and_teardowns_circuit: None,
                delegation_proofs: Default::default(),
                compiled_delegation_circuits: Default::default(),
                register_final_values: Vec::new(),
                final_pc: 0,
                final_timestamp: 4,
                end_params: [0; 8],
                recursion_chain_preimage: None,
                recursion_chain_hash: None,
                pow_challenge: 0,
                num_it_circuits: None,
            },
            setups: Setups::new(),
        }
    }

    /// The JSON Task S writes for a v4 artifact: no L1 keys.
    fn v4_value(mode: SoundnessMode) -> serde_json::Value {
        let mut value = serde_json::to_value(artifact(mode)).unwrap();
        value["schema_version"] = serde_json::json!(MODE_SCHEMA_VERSION);
        let object = value.as_object_mut().unwrap();
        object.remove("feeder_layers").unwrap();
        object.remove("l1").unwrap();
        value
    }

    /// Task S's v3 JSON: the v4 shape without a mode.
    fn v3_value() -> serde_json::Value {
        let mut value = v4_value(SoundnessMode::DEFAULT);
        value["schema_version"] = serde_json::json!(LEGACY_SCHEMA_VERSION);
        value
            .as_object_mut()
            .unwrap()
            .remove("soundness_mode")
            .unwrap();
        value
    }

    fn legacy_value(version: u32) -> serde_json::Value {
        match version {
            LEGACY_SCHEMA_VERSION => v3_value(),
            MODE_SCHEMA_VERSION => v4_value(SoundnessMode::DEFAULT),
            _ => unreachable!("not a legacy schema: {version}"),
        }
    }

    fn l1_artifact(mode: SoundnessMode, target: ProofTarget) -> ProofArtifact {
        let mut artifact = artifact(mode);
        artifact.target = target;
        artifact.feeder_layers = 3;
        artifact.chain_end_params = vec![[0; 8]; 6];
        artifact
    }

    /// The committed wrap bundle (no schema version of its own).
    fn fixture_bundle() -> L1Bundle {
        serde_json::from_slice(
            &std::fs::read(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("fixtures/l1_reference_2p21/l1_bundle.json"),
            )
            .unwrap(),
        )
        .unwrap()
    }

    fn decode_error(value: serde_json::Value) -> String {
        serde_json::from_value::<ProofArtifact>(value)
            .map(|_| ())
            .expect_err("the artifact must not decode")
            .to_string()
    }

    #[test]
    fn v4_requires_a_known_explicit_mode() {
        for &mode in SoundnessMode::ALL {
            let decoded: ProofArtifact = serde_json::from_value(v4_value(mode)).unwrap();
            assert_eq!(decoded.schema_version, 4);
            assert_eq!(decoded.soundness_mode, mode);
            assert_eq!((decoded.feeder_layers, decoded.l1.is_none()), (0, true));
            decoded.validate_expected_mode(mode).unwrap();
        }
        let mut value = v4_value(SoundnessMode::DEFAULT);
        value.as_object_mut().unwrap().remove("soundness_mode");
        assert!(serde_json::from_value::<ProofArtifact>(value.clone())
            .unwrap_err()
            .to_string()
            .contains("MissingSoundnessMode"));
        for invalid in [serde_json::Value::Null, serde_json::json!("unknown")] {
            value["soundness_mode"] = invalid;
            let expected_error = if value["soundness_mode"].is_null() {
                "MissingSoundnessMode"
            } else {
                "unknown variant"
            };
            assert!(serde_json::from_value::<ProofArtifact>(value.clone())
                .unwrap_err()
                .to_string()
                .contains(expected_error));
        }
    }

    #[test]
    fn v3_is_explicitly_legacy_pessimistic() {
        let mut value = v3_value();
        let decoded: ProofArtifact = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(decoded.schema_version, 3);
        assert_eq!(decoded.soundness_mode, SoundnessMode::PessimisticConjecture);
        assert_eq!((decoded.feeder_layers, decoded.l1.is_none()), (0, true));
        assert!(decoded
            .validate_expected_mode(SoundnessMode::EthproofsSoundnessCalc)
            .unwrap_err()
            .contains("SoundnessModeMismatch"));
        value["soundness_mode"] =
            serde_json::to_value(SoundnessMode::EthproofsSoundnessCalc).unwrap();
        assert!(serde_json::from_value::<ProofArtifact>(value)
            .unwrap_err()
            .to_string()
            .contains("ConflictingLegacySoundnessMode"));
    }

    #[test]
    fn unknown_schema_and_duplicate_metadata_are_rejected() {
        for version in [0, 2, 7, u32::MAX] {
            // A version error is explicit even without a proof payload.
            let value = serde_json::json!({"schema_version": version});
            assert!(serde_json::from_value::<ProofArtifact>(value)
                .unwrap_err()
                .to_string()
                .contains("UnsupportedArtifactVersion"));
        }
        let error =
            serde_json::from_str::<ProofArtifact>(r#"{"schema_version":4,"schema_version":3}"#)
                .unwrap_err();
        assert!(error.to_string().contains("duplicate field"));
    }

    /// v4 and v3 keep Task S's decode rules. An L1 target or L1 content, which Task S never
    /// wrote, is rejected precisely (Task S failed on the unknown target variant); the
    /// neutral L1 values that a v6-shaped writer emits for them are accepted.
    #[test]
    fn legacy_schemas_cannot_carry_an_l1_target() {
        for target in [ProofTarget::L1Feeder, ProofTarget::L1] {
            for version in [LEGACY_SCHEMA_VERSION, MODE_SCHEMA_VERSION] {
                let mut value = legacy_value(version);
                value["target"] = serde_json::to_value(target).unwrap();
                let error = decode_error(value);
                assert!(
                    error.contains(&format!(
                        "UnsupportedArtifactTarget: schema v{version} cannot carry the L1 target {target:?}"
                    )),
                    "{error}"
                );
                let mut in_memory = l1_artifact(SoundnessMode::DEFAULT, target);
                in_memory.schema_version = version;
                assert!(in_memory
                    .validate_schema()
                    .unwrap_err()
                    .starts_with("UnsupportedArtifactTarget:"));
            }
        }
        for version in [LEGACY_SCHEMA_VERSION, MODE_SCHEMA_VERSION] {
            let mut counted = legacy_value(version);
            counted["feeder_layers"] = serde_json::json!(2);
            let error = decode_error(counted);
            assert!(
                error.contains(&format!(
                    "UnsupportedArtifactField: schema v{version} has no L1 fields"
                )),
                "{error}"
            );
            let mut neutral = legacy_value(version);
            neutral["feeder_layers"] = serde_json::json!(0);
            neutral["l1"] = serde_json::Value::Null;
            let decoded: ProofArtifact = serde_json::from_value(neutral).unwrap();
            assert_eq!(decoded.schema_version, version);
            assert_eq!((decoded.feeder_layers, decoded.l1.is_none()), (0, true));
        }
        let mut counted = artifact(SoundnessMode::DEFAULT);
        counted.schema_version = MODE_SCHEMA_VERSION;
        counted.feeder_layers = 1;
        let mut bundled = artifact(SoundnessMode::DEFAULT);
        bundled.schema_version = MODE_SCHEMA_VERSION;
        bundled.l1 = Some(fixture_bundle());
        for in_memory in [counted, bundled] {
            assert!(in_memory
                .validate_schema()
                .unwrap_err()
                .starts_with("UnsupportedArtifactField:"));
        }
    }

    /// v5 is rejected by its number alone, whatever the other fields hold.
    #[test]
    fn v5_is_rejected_by_number() {
        let bare = serde_json::json!({"schema_version": 5});
        let mut relabelled = serde_json::to_value(l1_artifact(
            SoundnessMode::PessimisticConjecture,
            ProofTarget::L1Feeder,
        ))
        .unwrap();
        relabelled["schema_version"] = serde_json::json!(5);
        let mut v4_shaped = v4_value(SoundnessMode::PessimisticConjecture);
        v4_shaped["schema_version"] = serde_json::json!(5);
        for value in [bare, relabelled, v4_shaped] {
            assert!(decode_error(value).contains(PRE_REBASE_L1_ERROR));
        }
        let mut in_memory = artifact(SoundnessMode::PessimisticConjecture);
        in_memory.schema_version = PRE_REBASE_L1_SCHEMA_VERSION;
        assert_eq!(
            in_memory.validate_schema().unwrap_err(),
            PRE_REBASE_L1_ERROR
        );
        assert!(PRE_REBASE_L1_ERROR.contains("pre-rebase L1 artifact; unsupported; regenerate"));
    }

    #[test]
    fn v6_round_trips_with_and_without_l1_fields() {
        let bundle = fixture_bundle();
        let mut wrapped = l1_artifact(SoundnessMode::PessimisticConjecture, ProofTarget::L1);
        wrapped.l1 = Some(bundle);
        let mut cases = vec![
            l1_artifact(SoundnessMode::PessimisticConjecture, ProofTarget::L1Feeder),
            wrapped,
        ];
        cases.extend(SoundnessMode::ALL.iter().map(|&mode| artifact(mode)));
        for original in cases {
            let bytes = serde_json::to_vec(&original).unwrap();
            let decoded: ProofArtifact = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(decoded.schema_version, ARTIFACT_SCHEMA_VERSION);
            assert_eq!(decoded.soundness_mode, original.soundness_mode);
            assert_eq!(decoded.target, original.target);
            assert_eq!(decoded.feeder_layers, original.feeder_layers);
            assert_eq!(decoded.l1.is_some(), original.l1.is_some());
            assert_eq!(serde_json::to_vec(&decoded).unwrap(), bytes);
            decoded.validate_schema().unwrap();
        }
    }

    #[test]
    fn v6_requires_mode_and_feeder_layers() {
        let base = serde_json::to_value(l1_artifact(
            SoundnessMode::PessimisticConjecture,
            ProofTarget::L1Feeder,
        ))
        .unwrap();
        for invalid in [None, Some(serde_json::Value::Null)] {
            let mut value = base.clone();
            match invalid {
                None => {
                    value.as_object_mut().unwrap().remove("soundness_mode");
                }
                Some(null) => value["soundness_mode"] = null,
            }
            assert!(decode_error(value)
                .contains("MissingSoundnessMode: schema v6 requires soundness_mode"));
        }
        let mut value = base.clone();
        value.as_object_mut().unwrap().remove("feeder_layers");
        assert!(
            decode_error(value).contains("MissingFeederLayers: schema v6 requires feeder_layers")
        );
        let mut value = base;
        value["l1"] = serde_json::json!({"not": "a bundle"});
        decode_error(value);
    }

    #[test]
    fn expected_mode_rejection_precedes_source_loading() {
        let source =
            crate::ProgramSource::legacy_binaries_from_bin(Path::new("/missing/task-s.bin"));
        for &mode in SoundnessMode::ALL {
            let expected = SoundnessMode::ALL
                .iter()
                .copied()
                .find(|&other| other != mode)
                .unwrap();
            let error =
                crate::verify_artifact_in_mode(&artifact(mode), &source, expected).unwrap_err();
            assert!(error.starts_with("SoundnessModeMismatch:"), "{error}");
        }
    }
}
