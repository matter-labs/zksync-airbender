//! Paths and zlib-compressed typed JSON for committed proof fixtures.

use std::io::{Read, Write};
use std::path::{Path, PathBuf};

pub const MODES: [&str; 2] = ["pessimistic_conjecture", "ethproofs_soundcalc"];
pub const CIRCUITS: [&str; 14] = [
    "add_sub_lui_auipc_mop",
    "jump_branch_slt",
    "shift_binop",
    "unsigned_mul_div",
    "mem_word_only",
    "mem_subword_only",
    "inits_and_teardowns",
    "unified_reduced_machine",
    "bigint_with_extended_control",
    "blake2_with_extended_control",
    "keccak_special5",
    "keccak_column_parity",
    "keccak_theta_rho",
    "keccak_chi5",
];
pub const CHAINS: [&str; 4] = ["base", "unified", "unrolled", "unrolled_unified"];
/// Canonical special-profile circuits available only in pessimistic mode.
pub const PESSIMISTIC_CIRCUITS: [&str; 2] = ["compression", "compression_final"];
/// L1 chains exist only in pessimistic_conjecture.
pub const L1_CHAINS: [&str; 2] = ["compression", "l1"];

/// Repository root containing fixture data and its producer inputs.
pub fn root() -> PathBuf {
    if let Some(root) = std::env::var_os("AB_TEST_ARTIFACT_ROOT") {
        return root.into();
    }
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

/// Separate repository-shaped output root used by fixture regeneration checks.
pub fn output_root() -> PathBuf {
    std::env::var_os("PROOF_FIXTURES_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(root)
}

pub fn circuit_proof(mode_dir: &str, circuit: &str) -> PathBuf {
    circuit_proof_in(&root(), mode_dir, circuit)
}

pub fn circuit_proof_in(repository_root: &Path, mode_dir: &str, circuit: &str) -> PathBuf {
    assert!(
        MODES.contains(&mode_dir),
        "unknown soundness mode: {mode_dir}"
    );
    assert!(
        CIRCUITS.contains(&circuit)
            || (mode_dir == "pessimistic_conjecture" && PESSIMISTIC_CIRCUITS.contains(&circuit)),
        "unknown circuit/mode: {circuit}/{mode_dir}"
    );
    repository_root
        .join("fixtures/circuits")
        .join(mode_dir)
        .join(format!("{circuit}.json.zlib"))
}

pub fn chain_artifact(mode_dir: &str, chain: &str) -> PathBuf {
    assert!(
        MODES.contains(&mode_dir),
        "unknown soundness mode: {mode_dir}"
    );
    assert!(
        CHAINS.contains(&chain)
            || (mode_dir == "pessimistic_conjecture" && L1_CHAINS.contains(&chain)),
        "unknown chain for {mode_dir}: {chain}"
    );
    root()
        .join("fixtures/chains")
        .join(mode_dir)
        .join(format!("{chain}.json.zlib"))
}

/// Encode a fixture and return the finished writer so files can be synced before publication.
pub fn encode<T: serde::Serialize, W: Write>(value: &T, output: W) -> W {
    let mut encoder = flate2::write::ZlibEncoder::new(output, flate2::Compression::default());
    serde_json::to_writer(&mut encoder, value).expect("serialize fixture");
    encoder.finish().expect("finish fixture compression")
}

/// Decode a fixture written by [`encode`].
pub fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> T {
    serde_json::from_slice(&decode_json(bytes)).expect("deserialize fixture")
}

/// Decompress the original JSON bytes without changing their field order or formatting.
pub fn decode_json(bytes: &[u8]) -> Vec<u8> {
    let mut decoder = flate2::read::ZlibDecoder::new(bytes);
    let mut unpacked = Vec::new();
    decoder
        .read_to_end(&mut unpacked)
        .expect("decompress fixture");
    unpacked
}

pub fn write_file<T: serde::Serialize>(path: impl AsRef<Path>, value: &T) {
    let file = std::fs::File::create(path).expect("create fixture");
    encode(value, file).sync_all().expect("sync fixture");
}

pub fn read_file<T: serde::de::DeserializeOwned>(path: impl AsRef<Path>) -> T {
    decode(&std::fs::read(path).expect("read fixture"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn assert_inventory(directory: &Path, stems: &[&str], pessimistic_extra: &[&str]) {
        let modes: BTreeSet<_> = std::fs::read_dir(directory)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect();
        assert_eq!(modes, MODES.map(str::to_owned).into());
        for mode in MODES {
            let actual: BTreeSet<_> = std::fs::read_dir(directory.join(mode))
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .collect();
            let extra = if mode == "pessimistic_conjecture" {
                pessimistic_extra
            } else {
                &[]
            };
            let expected: BTreeSet<_> = stems
                .iter()
                .chain(extra)
                .map(|stem| directory.join(mode).join(format!("{stem}.json.zlib")))
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn committed_fixture_inventory() {
        assert_inventory(
            &root().join("fixtures/circuits"),
            &CIRCUITS,
            &PESSIMISTIC_CIRCUITS,
        );
        assert_inventory(&root().join("fixtures/chains"), &CHAINS, &L1_CHAINS);
    }
}
