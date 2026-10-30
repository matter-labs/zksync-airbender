//! Mode-tagged standalone proof/setup checkpoints. Raw legacy pairs are pessimistic only.

use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::{ProvingSelection, SecurityLevel, SoundnessMode};
use serde::{Deserialize, Serialize};
use setups::Setups;
use std::path::Path;

pub const PROGRAM_PROOF_BUNDLE_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProgramProofBundleV1 {
    #[serde(deserialize_with = "deserialize_bundle_version")]
    pub schema_version: u32,
    pub security_level: SecurityLevel,
    pub soundness_mode: SoundnessMode,
    pub proof: ProgramProof,
    pub setups: Setups,
}

fn deserialize_bundle_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != PROGRAM_PROOF_BUNDLE_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(format!(
            "UnsupportedProofBundleVersion: {version}"
        )));
    }
    Ok(version)
}

impl ProgramProofBundleV1 {
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        validate_header(
            self.schema_version,
            self.security_level,
            self.soundness_mode,
            expected,
        )
    }

    pub fn into_parts(self) -> (ProgramProof, Setups) {
        (self.proof, self.setups)
    }
}

fn validate_header(
    version: u32,
    security: SecurityLevel,
    mode: SoundnessMode,
    expected: SoundnessMode,
) -> Result<(), String> {
    if version != PROGRAM_PROOF_BUNDLE_SCHEMA_VERSION {
        return Err(format!("UnsupportedProofBundleVersion: {version}"));
    }
    if security != SecurityLevel::Sec100 {
        return Err(format!("UnsupportedProofBundleSecurityLevel: {security:?}"));
    }
    if mode != expected {
        return Err(format!(
            "SoundnessModeMismatch: expected {expected:?}, bundle is {mode:?}"
        ));
    }
    Ok(())
}

/// Read a tagged bundle. No legacy fallback is attempted on a malformed bundle.
pub fn read_program_proof_bundle(
    path: &Path,
    expected: SoundnessMode,
) -> Result<ProgramProofBundleV1, String> {
    let file =
        std::fs::File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    let bundle: ProgramProofBundleV1 = serde_json::from_reader(std::io::BufReader::new(file))
        .map_err(|error| format!("decode proof bundle {}: {error}", path.display()))?;
    bundle.validate_expected_mode(expected)?;
    Ok(bundle)
}

/// Write new checkpoints with an explicit selection and both payloads in one envelope.
pub fn write_program_proof_bundle(
    path: &Path,
    selection: ProvingSelection,
    proof: &ProgramProof,
    setups: &Setups,
) -> Result<(), String> {
    #[derive(Serialize)]
    struct BundleRef<'a> {
        schema_version: u32,
        security_level: SecurityLevel,
        soundness_mode: SoundnessMode,
        proof: &'a ProgramProof,
        setups: &'a Setups,
    }
    let bundle = BundleRef {
        schema_version: PROGRAM_PROOF_BUNDLE_SCHEMA_VERSION,
        security_level: selection.security_level,
        soundness_mode: selection.soundness_mode,
        proof,
        setups,
    };
    let file = std::fs::File::create(path)
        .map_err(|error| format!("create {}: {error}", path.display()))?;
    let mut writer = std::io::BufWriter::new(file);
    serde_json::to_writer(&mut writer, &bundle)
        .map_err(|error| format!("write proof bundle {}: {error}", path.display()))?;
    std::io::Write::flush(&mut writer)
        .map_err(|error| format!("flush proof bundle {}: {error}", path.display()))
}

/// Legacy pairs have no functioning decoder at this revision; use the JSON bundle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum L1InputError {
    LegacyBincodeUnsupported,
}

impl std::fmt::Display for L1InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LegacyBincodeUnsupported => f.write_str(
                "legacy bincode proof pairs are not decodable at this revision; use --bundle",
            ),
        }
    }
}
impl std::error::Error for L1InputError {}

/// Explicitly reject the retired legacy pair syntax before any file I/O.
#[cfg(feature = "l1")]
pub fn read_l1_input(
    _proof: &Path,
    _setups: &Path,
    _expected: SoundnessMode,
) -> Result<(ProgramProof, Setups), L1InputError> {
    Err(L1InputError::LegacyBincodeUnsupported)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) fn empty_proof() -> ProgramProof {
        ProgramProof {
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
        }
    }

    fn temp_dir() -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "airbender-proof-bundle-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        dir
    }

    #[test]
    fn tagged_bundles_require_the_callers_mode() {
        let dir = temp_dir();
        let path = dir.join("bundle.json");
        for &mode in SoundnessMode::ALL {
            write_program_proof_bundle(
                &path,
                ProvingSelection {
                    soundness_mode: mode,
                    ..ProvingSelection::default()
                },
                &empty_proof(),
                &Setups::new(),
            )
            .unwrap();
            let bundle = read_program_proof_bundle(&path, mode).unwrap();
            assert_eq!(bundle.schema_version, 1);
            assert_eq!(bundle.soundness_mode, mode);
            let other = SoundnessMode::ALL
                .iter()
                .copied()
                .find(|&other| other != mode)
                .unwrap();
            assert!(read_program_proof_bundle(&path, other)
                .unwrap_err()
                .contains("SoundnessModeMismatch"));
        }
        std::fs::write(&path, r#"{"schema_version":2,"security_level":"Sec100","soundness_mode":"PessimisticConjecture"}"#).unwrap();
        assert!(read_program_proof_bundle(&path, SoundnessMode::DEFAULT)
            .unwrap_err()
            .contains("UnsupportedProofBundleVersion"));
        std::fs::write(&path, r#"{"schema_version":1,"security_level":"Sec100"}"#).unwrap();
        assert!(read_program_proof_bundle(&path, SoundnessMode::DEFAULT)
            .unwrap_err()
            .contains("soundness_mode"));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(feature = "l1")]
    #[test]
    fn legacy_pairs_report_a_typed_error_without_io() {
        let missing = Path::new("/missing/task-s-legacy.bin");
        for &mode in SoundnessMode::ALL {
            let error = read_l1_input(missing, missing, mode).unwrap_err();
            assert_eq!(error, L1InputError::LegacyBincodeUnsupported);
            assert_eq!(
                error.to_string(),
                "legacy bincode proof pairs are not decodable at this revision; use --bundle"
            );
        }
    }
}
