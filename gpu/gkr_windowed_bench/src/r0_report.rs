use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::r0_artifact::FrozenR0Shape;
use crate::r0_geometry::{R0Geometry, R0LaunchMetadata, R0MemoryPreflight};
use crate::r0_input::FrozenE4;

pub const R0_REPORT_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0Traversal {
    Forward,
    Reverse,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0ResultKey {
    pub point: String,
    pub circuit: String,
    pub layer: u32,
    pub log_trace: u32,
    pub seed: u64,
    pub geometry: R0Geometry,
    pub traversal: Option<R0Traversal>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0Bindings {
    pub bundle_sha256: String,
    pub coordinate_sha256: String,
    pub input_sha256: String,
    pub source_data_sha256: String,
    pub independent_source_sha256: String,
    pub derived_source_sha256: Option<String>,
    pub challenge_sha256: String,
    pub equality_point_sha256: String,
    pub direct_eq_sha256: String,
    pub factored_eq_sha256: String,
    pub coefficient_sha256: String,
    pub executable_sha256: String,
    pub source_tree_sha256: String,
    pub build_flags_sha256: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0CheckpointState {
    Started,
    Complete,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0CheckpointV1 {
    pub version: u32,
    pub key: R0ResultKey,
    pub bindings: R0Bindings,
    pub state: R0CheckpointState,
    pub rows_sha256: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R0ObservationRowV1 {
    pub version: u32,
    pub key: R0ResultKey,
    pub bindings: R0Bindings,
    pub production_rows: u64,
    pub shape: FrozenR0Shape,
    pub preflight: Option<R0MemoryPreflight>,
    pub launch: Option<R0LaunchMetadata>,
    pub cells: Option<[FrozenE4; 27]>,
    pub checksum: Option<String>,
    pub failure: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R0TimingSampleV1 {
    pub key: R0ResultKey,
    pub sample_index: u32,
    pub warmup: bool,
    pub milliseconds: f64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0RowsKind {
    Observation,
    Timing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0CheckpointReuse {
    Execute,
    Complete,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0ReportError(String);

impl core::fmt::Display for R0ReportError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for R0ReportError {}

fn report_error(message: impl Into<String>) -> R0ReportError {
    R0ReportError(message.into())
}

pub fn begin_checkpoint(
    checkpoint_path: &Path,
    rows_path: &Path,
    key: &R0ResultKey,
    bindings: &R0Bindings,
    resume: bool,
) -> Result<R0CheckpointReuse, R0ReportError> {
    validate_bindings(bindings)?;
    if checkpoint_path.exists() {
        let existing = read_checkpoint(checkpoint_path)?;
        validate_checkpoint_identity(&existing, key, bindings)?;
        match existing.state {
            R0CheckpointState::Complete => {
                return Err(report_error(format!(
                    "complete checkpoint is immutable: {}",
                    checkpoint_path.display()
                )));
            }
            R0CheckpointState::Started if !resume => {
                return Err(report_error(format!(
                    "started checkpoint requires explicit resume: {}",
                    checkpoint_path.display()
                )));
            }
            R0CheckpointState::Started => {
                if !existing.rows_sha256.is_empty() {
                    return Err(report_error("started checkpoint has a nonempty rows hash"));
                }
            }
        }
    } else if rows_path.exists() && !resume {
        return Err(report_error(format!(
            "rows file exists without a checkpoint: {}",
            rows_path.display()
        )));
    }

    atomic_write(rows_path, &[])?;
    let started = R0CheckpointV1 {
        version: R0_REPORT_VERSION,
        key: key.clone(),
        bindings: bindings.clone(),
        state: R0CheckpointState::Started,
        rows_sha256: String::new(),
    };
    atomic_write_json(checkpoint_path, &started)?;
    Ok(R0CheckpointReuse::Execute)
}

pub fn complete_checkpoint(
    checkpoint_path: &Path,
    rows_path: &Path,
    key: &R0ResultKey,
    bindings: &R0Bindings,
    rows_kind: R0RowsKind,
) -> Result<(), R0ReportError> {
    let started = read_checkpoint(checkpoint_path)?;
    validate_checkpoint_identity(&started, key, bindings)?;
    if started.state != R0CheckpointState::Started || !started.rows_sha256.is_empty() {
        return Err(report_error("checkpoint is not a clean Started record"));
    }
    validate_rows_file(rows_path, rows_kind, Some((key, bindings)))?;
    let rows_sha256 = sha256_file(rows_path)?;
    let complete = R0CheckpointV1 {
        state: R0CheckpointState::Complete,
        rows_sha256,
        ..started
    };
    atomic_write_json(checkpoint_path, &complete)
}

pub fn verify_reusable_checkpoint(
    checkpoint_path: &Path,
    rows_path: &Path,
    key: &R0ResultKey,
    bindings: &R0Bindings,
    rows_kind: R0RowsKind,
) -> Result<R0CheckpointReuse, R0ReportError> {
    let checkpoint = read_checkpoint(checkpoint_path)?;
    validate_checkpoint_identity(&checkpoint, key, bindings)?;
    if checkpoint.state != R0CheckpointState::Complete {
        return Err(report_error("only a Complete checkpoint is reusable"));
    }
    validate_sha256("rows_sha256", &checkpoint.rows_sha256)?;
    validate_rows_file(rows_path, rows_kind, Some((key, bindings)))?;
    let actual = sha256_file(rows_path)?;
    if actual != checkpoint.rows_sha256 {
        return Err(report_error(format!(
            "rows hash mismatch: expected {}, got {actual}",
            checkpoint.rows_sha256
        )));
    }
    Ok(R0CheckpointReuse::Complete)
}

pub fn write_jsonl_atomic<T: Serialize>(path: &Path, rows: &[T]) -> Result<(), R0ReportError> {
    let mut bytes = Vec::new();
    for row in rows {
        serde_json::to_writer(&mut bytes, row)
            .map_err(|error| report_error(format!("serialize JSONL row: {error}")))?;
        bytes.push(b'\n');
    }
    atomic_write(path, &bytes)
}

pub fn read_observation_rows(path: &Path) -> Result<Vec<R0ObservationRowV1>, R0ReportError> {
    let rows = read_jsonl(path)?;
    validate_observation_rows(&rows)?;
    Ok(rows)
}

pub fn read_timing_samples(path: &Path) -> Result<Vec<R0TimingSampleV1>, R0ReportError> {
    let rows = read_jsonl(path)?;
    validate_timing_samples(&rows)?;
    Ok(rows)
}

pub fn validate_observation_rows(rows: &[R0ObservationRowV1]) -> Result<(), R0ReportError> {
    if rows.is_empty() {
        return Err(report_error("observation file has no rows"));
    }
    for (index, row) in rows.iter().enumerate() {
        if row.version != R0_REPORT_VERSION {
            return Err(report_error(format!(
                "observation row {index} has unsupported version {}",
                row.version
            )));
        }
        let success = row.launch.is_some()
            && row.cells.is_some()
            && row.checksum.is_some()
            && row.failure.is_none();
        let failure = row.launch.is_none()
            && row.cells.is_none()
            && row.checksum.is_none()
            && row
                .failure
                .as_ref()
                .is_some_and(|failure| !failure.is_empty());
        if !success && !failure {
            return Err(report_error(format!(
                "observation row {index} mixes success and failure fields"
            )));
        }
    }
    Ok(())
}

pub fn validate_timing_samples(rows: &[R0TimingSampleV1]) -> Result<(), R0ReportError> {
    if rows.is_empty() {
        return Err(report_error("timing file has no rows"));
    }
    let mut next_forward = 0u32;
    let mut next_reverse = 0u32;
    for (index, row) in rows.iter().enumerate() {
        if !row.milliseconds.is_finite() || row.milliseconds < 0.0 {
            return Err(report_error(format!(
                "timing row {index} has a non-finite or negative duration"
            )));
        }
        let expected = match row.key.traversal {
            Some(R0Traversal::Forward) => &mut next_forward,
            Some(R0Traversal::Reverse) => &mut next_reverse,
            None => return Err(report_error(format!("timing row {index} has no traversal"))),
        };
        if row.sample_index != *expected {
            return Err(report_error(format!(
                "timing row {index} has sample index {}, expected {}",
                row.sample_index, *expected
            )));
        }
        let expected_warmup = row.sample_index < 5;
        if row.warmup != expected_warmup {
            return Err(report_error(format!(
                "timing row {index} has warmup={}, expected {expected_warmup}",
                row.warmup
            )));
        }
        *expected = expected
            .checked_add(1)
            .ok_or_else(|| report_error("timing sample index overflow"))?;
    }
    for (traversal, count) in [("forward", next_forward), ("reverse", next_reverse)] {
        if count != 0 && count != 55 {
            return Err(report_error(format!(
                "{traversal} traversal has {count} rows, expected 55"
            )));
        }
    }
    Ok(())
}

pub fn aggregate_timing_median_ms(rows: &[R0TimingSampleV1]) -> Result<f64, R0ReportError> {
    validate_timing_samples(rows)?;
    let Some(first) = rows.first() else {
        return Err(report_error("timing file has no rows"));
    };
    if rows.iter().any(|row| {
        row.key.point != first.key.point
            || row.key.circuit != first.key.circuit
            || row.key.layer != first.key.layer
            || row.key.log_trace != first.key.log_trace
            || row.key.seed != first.key.seed
            || row.key.geometry != first.key.geometry
    }) {
        return Err(report_error("aggregate timing rows have mixed keys"));
    }
    let forward = rows
        .iter()
        .filter(|row| row.key.traversal == Some(R0Traversal::Forward))
        .count();
    let reverse = rows
        .iter()
        .filter(|row| row.key.traversal == Some(R0Traversal::Reverse))
        .count();
    if forward != 55 || reverse != 55 {
        return Err(report_error(format!(
            "aggregate timing requires 55 forward and 55 reverse rows, got {forward}/{reverse}"
        )));
    }
    let mut samples = rows
        .iter()
        .filter(|row| !row.warmup)
        .map(|row| row.milliseconds)
        .collect::<Vec<_>>();
    if samples.len() != 100 {
        return Err(report_error(format!(
            "aggregate timing requires 100 measured samples, got {}",
            samples.len()
        )));
    }
    samples.sort_by(f64::total_cmp);
    Ok((samples[49] + samples[50]) / 2.0)
}

fn validate_rows_file(
    path: &Path,
    kind: R0RowsKind,
    expected: Option<(&R0ResultKey, &R0Bindings)>,
) -> Result<(), R0ReportError> {
    match kind {
        R0RowsKind::Observation => {
            let rows = read_jsonl::<R0ObservationRowV1>(path)?;
            validate_observation_rows(&rows)?;
            if let Some((key, bindings)) = expected {
                if rows
                    .iter()
                    .any(|row| row.key != *key || row.bindings != *bindings)
                {
                    return Err(report_error(
                        "observation row key/bindings differ from checkpoint",
                    ));
                }
            }
        }
        R0RowsKind::Timing => {
            let rows = read_jsonl::<R0TimingSampleV1>(path)?;
            validate_timing_samples(&rows)?;
            if let Some((key, _)) = expected {
                if rows.iter().any(|row| {
                    row.key.point != key.point
                        || row.key.circuit != key.circuit
                        || row.key.layer != key.layer
                        || row.key.log_trace != key.log_trace
                        || row.key.seed != key.seed
                        || row.key.geometry != key.geometry
                        || row.key.traversal != key.traversal
                }) {
                    return Err(report_error("timing row key differs from checkpoint"));
                }
            }
        }
    }
    Ok(())
}

fn read_jsonl<T: DeserializeOwned>(path: &Path) -> Result<Vec<T>, R0ReportError> {
    let bytes = fs::read(path)
        .map_err(|error| report_error(format!("read {}: {error}", path.display())))?;
    serde_json::Deserializer::from_slice(&bytes)
        .into_iter::<T>()
        .map(|row| row.map_err(|error| report_error(format!("parse JSONL: {error}"))))
        .collect()
}

fn read_checkpoint(path: &Path) -> Result<R0CheckpointV1, R0ReportError> {
    let bytes = fs::read(path)
        .map_err(|error| report_error(format!("read {}: {error}", path.display())))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| report_error(format!("parse checkpoint {}: {error}", path.display())))
}

fn validate_checkpoint_identity(
    checkpoint: &R0CheckpointV1,
    key: &R0ResultKey,
    bindings: &R0Bindings,
) -> Result<(), R0ReportError> {
    if checkpoint.version != R0_REPORT_VERSION {
        return Err(report_error(format!(
            "unsupported checkpoint version {}",
            checkpoint.version
        )));
    }
    validate_bindings(&checkpoint.bindings)?;
    if checkpoint.key != *key {
        return Err(report_error("checkpoint key mismatch"));
    }
    if checkpoint.bindings != *bindings {
        return Err(report_error("checkpoint binding mismatch"));
    }
    Ok(())
}

fn validate_bindings(bindings: &R0Bindings) -> Result<(), R0ReportError> {
    for (name, value) in [
        ("bundle_sha256", bindings.bundle_sha256.as_str()),
        ("coordinate_sha256", bindings.coordinate_sha256.as_str()),
        ("input_sha256", bindings.input_sha256.as_str()),
        ("source_data_sha256", bindings.source_data_sha256.as_str()),
        (
            "independent_source_sha256",
            bindings.independent_source_sha256.as_str(),
        ),
        ("challenge_sha256", bindings.challenge_sha256.as_str()),
        (
            "equality_point_sha256",
            bindings.equality_point_sha256.as_str(),
        ),
        ("direct_eq_sha256", bindings.direct_eq_sha256.as_str()),
        ("factored_eq_sha256", bindings.factored_eq_sha256.as_str()),
        ("coefficient_sha256", bindings.coefficient_sha256.as_str()),
        ("executable_sha256", bindings.executable_sha256.as_str()),
        ("source_tree_sha256", bindings.source_tree_sha256.as_str()),
        ("build_flags_sha256", bindings.build_flags_sha256.as_str()),
    ] {
        validate_sha256(name, value)?;
    }
    if let Some(value) = &bindings.derived_source_sha256 {
        validate_sha256("derived_source_sha256", value)?;
    }
    Ok(())
}

fn validate_sha256(name: &str, value: &str) -> Result<(), R0ReportError> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(report_error(format!("{name} is not lowercase SHA-256")));
    }
    Ok(())
}

fn atomic_write_json<T: Serialize>(path: &Path, value: &T) -> Result<(), R0ReportError> {
    let mut bytes = serde_json::to_vec(value)
        .map_err(|error| report_error(format!("serialize checkpoint: {error}")))?;
    bytes.push(b'\n');
    atomic_write(path, &bytes)
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), R0ReportError> {
    let parent = path
        .parent()
        .ok_or_else(|| report_error(format!("{} has no parent", path.display())))?;
    fs::create_dir_all(parent)
        .map_err(|error| report_error(format!("create {}: {error}", parent.display())))?;
    let temp = temporary_path(path)?;
    let result = (|| {
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temp)
            .map_err(|error| report_error(format!("create {}: {error}", temp.display())))?;
        file.write_all(bytes)
            .map_err(|error| report_error(format!("write {}: {error}", temp.display())))?;
        file.sync_all()
            .map_err(|error| report_error(format!("fsync {}: {error}", temp.display())))?;
        fs::rename(&temp, path).map_err(|error| {
            report_error(format!(
                "rename {} to {}: {error}",
                temp.display(),
                path.display()
            ))
        })?;
        File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| report_error(format!("fsync {}: {error}", parent.display())))?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result
}

fn temporary_path(path: &Path) -> Result<PathBuf, R0ReportError> {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| report_error(format!("{} has no UTF-8 filename", path.display())))?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| report_error(format!("system clock: {error}")))?
        .as_nanos();
    Ok(path.with_file_name(format!(".{file_name}.tmp.{}.{nonce}", std::process::id())))
}

fn sha256_file(path: &Path) -> Result<String, R0ReportError> {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| report_error(format!("run sha256sum: {error}")))?;
    if !output.status.success() {
        return Err(report_error(format!(
            "sha256sum failed for {}",
            path.display()
        )));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|error| report_error(format!("sha256sum output: {error}")))?;
    let hash = stdout.split_whitespace().next().unwrap_or_default();
    validate_sha256("sha256sum output", hash)?;
    Ok(hash.to_owned())
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use crate::r0_artifact::FrozenR0Shape;
    use crate::r0_geometry::R0Geometry;

    use super::*;

    fn temp_dir(label: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "gpu-gkr-windowed-task9-{label}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        path
    }

    fn key(traversal: Option<R0Traversal>) -> R0ResultKey {
        R0ResultKey {
            point: "natural".to_owned(),
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layer: 0,
            log_trace: 24,
            seed: 0xdead_beef_cafe_babe,
            geometry: R0Geometry::Cta288Pair,
            traversal,
        }
    }

    fn bindings(input: &str) -> R0Bindings {
        R0Bindings {
            bundle_sha256: "01".repeat(32),
            coordinate_sha256: "02".repeat(32),
            input_sha256: input.repeat(64 / input.len()),
            source_data_sha256: "04".repeat(32),
            independent_source_sha256: "05".repeat(32),
            derived_source_sha256: None,
            challenge_sha256: "06".repeat(32),
            equality_point_sha256: "07".repeat(32),
            direct_eq_sha256: "08".repeat(32),
            factored_eq_sha256: "09".repeat(32),
            coefficient_sha256: "0a".repeat(32),
            executable_sha256: "0b".repeat(32),
            source_tree_sha256: "0c".repeat(32),
            build_flags_sha256: "0d".repeat(32),
        }
    }

    fn shape() -> FrozenR0Shape {
        FrozenR0Shape {
            records: 1,
            projections: 1,
            bf_atoms: 1,
            e4_atoms: 0,
            source_uses: 1,
            unique_sources: 1,
            windows: 1,
            max_relative_column: 0,
            coefficient_recipes: 0,
            immediates: 0,
        }
    }

    #[test]
    fn cpu_complete_checkpoint_is_immutable_and_hash_verified() {
        let dir = temp_dir("complete");
        let checkpoint_path = dir.join("checkpoint.json");
        let rows_path = dir.join("rows.jsonl");
        let expected_key = key(None);
        let expected_bindings = bindings("03");

        begin_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            false,
        )
        .unwrap();
        let row = R0ObservationRowV1 {
            version: 1,
            key: expected_key.clone(),
            bindings: expected_bindings.clone(),
            production_rows: 1 << 21,
            shape: shape(),
            preflight: None,
            launch: None,
            cells: None,
            checksum: None,
            failure: Some("preflight-capacity: requested=2 free=1".to_owned()),
        };
        write_jsonl_atomic(&rows_path, &[row]).unwrap();
        complete_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            R0RowsKind::Observation,
        )
        .unwrap();

        assert_eq!(
            verify_reusable_checkpoint(
                &checkpoint_path,
                &rows_path,
                &expected_key,
                &expected_bindings,
                R0RowsKind::Observation,
            )
            .unwrap(),
            R0CheckpointReuse::Complete
        );
        assert!(begin_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            true,
        )
        .is_err());
        fs::write(&rows_path, b"tampered\n").unwrap();
        assert!(verify_reusable_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            R0RowsKind::Observation,
        )
        .is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn cpu_started_checkpoint_is_not_reusable_or_appended() {
        let dir = temp_dir("started");
        let checkpoint_path = dir.join("checkpoint.json");
        let rows_path = dir.join("rows.jsonl");
        let expected_key = key(None);
        let expected_bindings = bindings("03");
        begin_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            false,
        )
        .unwrap();
        fs::write(&rows_path, b"partial\n").unwrap();

        assert!(verify_reusable_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            R0RowsKind::Observation,
        )
        .is_err());
        assert!(begin_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &bindings("0e"),
            true,
        )
        .is_err());
        assert_eq!(
            begin_checkpoint(
                &checkpoint_path,
                &rows_path,
                &expected_key,
                &expected_bindings,
                true,
            )
            .unwrap(),
            R0CheckpointReuse::Execute
        );
        assert_eq!(fs::read(&rows_path).unwrap(), Vec::<u8>::new());
        let checkpoint: R0CheckpointV1 =
            serde_json::from_slice(&fs::read(&checkpoint_path).unwrap()).unwrap();
        assert_eq!(checkpoint.state, R0CheckpointState::Started);
        assert!(checkpoint.rows_sha256.is_empty());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn cpu_timing_rows_require_traversal_contiguous_indices_and_finite_values() {
        let rows = (0..55)
            .map(|sample_index| R0TimingSampleV1 {
                key: key(Some(R0Traversal::Forward)),
                sample_index,
                warmup: sample_index < 5,
                milliseconds: 0.25 + f64::from(sample_index) / 100.0,
            })
            .collect::<Vec<_>>();
        validate_timing_samples(&rows).unwrap();
        let mut bad_index = rows.clone();
        bad_index[1].sample_index = 2;
        assert!(validate_timing_samples(&bad_index).is_err());
        let mut bad_value = rows.clone();
        bad_value[1].milliseconds = f64::NAN;
        assert!(validate_timing_samples(&bad_value).is_err());
        let mut no_traversal = rows;
        no_traversal[0].key.traversal = None;
        assert!(validate_timing_samples(&no_traversal).is_err());
    }

    #[test]
    fn cpu_timing_checkpoint_rejects_opposite_traversal_rows() {
        let dir = temp_dir("timing-traversal-key");
        let checkpoint_path = dir.join("checkpoint.json");
        let rows_path = dir.join("rows.jsonl");
        let expected_key = key(Some(R0Traversal::Forward));
        let expected_bindings = bindings("03");
        begin_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            false,
        )
        .unwrap();
        let rows = (0..55)
            .map(|sample_index| R0TimingSampleV1 {
                key: key(Some(R0Traversal::Reverse)),
                sample_index,
                warmup: sample_index < 5,
                milliseconds: f64::from(sample_index + 1),
            })
            .collect::<Vec<_>>();
        write_jsonl_atomic(&rows_path, &rows).unwrap();
        assert!(complete_checkpoint(
            &checkpoint_path,
            &rows_path,
            &expected_key,
            &expected_bindings,
            R0RowsKind::Timing,
        )
        .is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn cpu_timing_rows_require_exact_warmup_and_sample_cardinality() {
        let rows = (0..55)
            .map(|sample_index| R0TimingSampleV1 {
                key: key(Some(R0Traversal::Forward)),
                sample_index,
                warmup: sample_index < 5,
                milliseconds: f64::from(sample_index + 1),
            })
            .collect::<Vec<_>>();
        assert!(validate_timing_samples(&rows[..54]).is_err());
        let mut late_warmup = rows.clone();
        late_warmup[5].warmup = true;
        assert!(validate_timing_samples(&late_warmup).is_err());
        let mut early_sample = rows;
        early_sample[4].warmup = false;
        assert!(validate_timing_samples(&early_sample).is_err());
    }

    #[test]
    fn cpu_timing_median_uses_only_the_hundred_forward_reverse_samples() {
        let mut rows = Vec::new();
        for traversal in [R0Traversal::Forward, R0Traversal::Reverse] {
            rows.extend((0..55).map(|sample_index| R0TimingSampleV1 {
                key: key(Some(traversal)),
                sample_index,
                warmup: sample_index < 5,
                milliseconds: if sample_index < 5 {
                    10_000.0
                } else {
                    f64::from(sample_index - 4)
                },
            }));
        }
        assert_eq!(aggregate_timing_median_ms(&rows).unwrap(), 25.5);
        rows.pop();
        assert!(aggregate_timing_median_ms(&rows).is_err());
    }
}
