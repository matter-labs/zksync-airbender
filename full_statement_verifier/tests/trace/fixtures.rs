use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use full_statement_verifier::host_utils::fixture_codec;
use verifier_common::fsv_binaries::FsvProgram;

pub struct Fixture {
    /// Absolute filename prefix, unique even when pooling several directories.
    pub name: String,
    pub program: FsvProgram,
}

const DEFAULT_FIXTURES: &[(&str, bool)] = &[
    ("keccak_f1600", true),
    ("base", true),
    ("base_alt", true),
    ("recursion0", false),
    ("recursion1", false),
    ("memory_windows", true),
    ("memory_windows_recursion", false),
];

pub fn directories() -> Vec<PathBuf> {
    let dirs: Vec<_> = if let Some(value) = std::env::var_os("COST_MODEL_FIXTURE_DIRS") {
        std::env::split_paths(&value).collect()
    } else {
        vec![std::env::var_os("COST_MODEL_FIXTURE_DIR")
            .map(PathBuf::from)
            .expect("set COST_MODEL_FIXTURE_DIR; see tests/cost_model_trace.rs")]
    };
    assert!(!dirs.is_empty(), "empty calibration corpus");
    dirs.into_iter()
        .map(|dir| std::fs::canonicalize(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())))
        .collect()
}

/// The generator writes zlib-JSON `(name, is_base_layer)` pairs only after all
/// outputs verify. Legacy directories without a manifest must contain exactly
/// the original seven pairs, so extra corpus inputs cannot be silently skipped.
fn in_directory(dir: &Path) -> Vec<Fixture> {
    let manifest = dir.join("fixtures_manifest.bin");
    let entries: Vec<(String, bool)> = if manifest.exists() {
        fixture_codec::decode(&std::fs::read(&manifest).expect("read fixture manifest"))
    } else {
        DEFAULT_FIXTURES
            .iter()
            .map(|(name, base)| ((*name).to_owned(), *base))
            .collect()
    };
    let mut names = BTreeSet::new();
    for (name, _) in &entries {
        assert!(
            !name.is_empty()
                && name
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-'),
            "invalid fixture name {name:?}"
        );
        assert!(names.insert(name.clone()), "duplicate fixture {name}");
        for suffix in ["proof", "setups"] {
            let path = dir.join(format!("{name}_{suffix}.bin"));
            assert!(path.is_file(), "missing {}", path.display());
        }
    }
    for (name, base) in DEFAULT_FIXTURES {
        assert!(
            entries
                .iter()
                .any(|(n, b)| n.as_str() == *name && b == base),
            "missing or misclassified required fixture {name}"
        );
    }
    for entry in std::fs::read_dir(dir).expect("list calibration corpus") {
        let file = entry.expect("read calibration entry").file_name();
        let file = file.to_str().expect("non-UTF8 calibration filename");
        if let Some(name) = file.strip_suffix("_proof.bin") {
            assert!(
                names.contains(name),
                "unlisted fixture {name}; regenerate its manifest"
            );
        }
    }
    entries
        .into_iter()
        .map(|(name, base)| Fixture {
            name: dir
                .join(name)
                .to_str()
                .expect("non-UTF8 fixture path")
                .to_owned(),
            program: if base {
                FsvProgram::UnrolledBaseLayer
            } else {
                FsvProgram::UnrolledRecursionLayer
            },
        })
        .collect()
}

pub fn all_fixtures() -> Vec<Fixture> {
    let dirs = directories();
    let unique: BTreeSet<_> = dirs.iter().collect();
    assert_eq!(unique.len(), dirs.len(), "duplicate calibration directory");
    dirs.iter().flat_map(|dir| in_directory(dir)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifests_include_extra_inputs_and_reject_omissions() {
        let dir = std::env::temp_dir().join(format!("cal-fixtures-{}", std::process::id()));
        std::fs::create_dir(&dir).expect("create fixture discovery test directory");
        let mut entries: Vec<_> = DEFAULT_FIXTURES
            .iter()
            .map(|(n, b)| ((*n).to_owned(), *b))
            .collect();
        for (name, _) in &entries {
            for suffix in ["proof", "setups"] {
                std::fs::write(dir.join(format!("{name}_{suffix}.bin")), [0]).unwrap();
            }
        }
        assert_eq!(in_directory(&dir).len(), 7);
        for suffix in ["proof", "setups"] {
            std::fs::write(dir.join(format!("base_123_{suffix}.bin")), [0]).unwrap();
        }
        assert!(std::panic::catch_unwind(|| in_directory(&dir)).is_err());
        entries.push(("base_123".to_owned(), true));
        let manifest = dir.join("fixtures_manifest.bin");
        std::fs::write(&manifest, fixture_codec::encode(&entries, Vec::new())).unwrap();
        assert_eq!(in_directory(&dir).len(), 8);
        entries.push(("base_123".to_owned(), true));
        std::fs::write(&manifest, fixture_codec::encode(&entries, Vec::new())).unwrap();
        assert!(std::panic::catch_unwind(|| in_directory(&dir)).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
