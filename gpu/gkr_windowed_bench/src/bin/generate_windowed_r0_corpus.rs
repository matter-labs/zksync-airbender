use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use clap::Parser;
use gpu_gkr_windowed_bench::r0_artifact::encode_r0_bundle;
use gpu_gkr_windowed_bench::r0_corpus::{generate_r0_bundle, r0_manifest_json};

#[derive(Parser)]
struct Args {
    #[arg(long, conflicts_with = "check")]
    write: bool,
    #[arg(long, conflicts_with = "write")]
    check: bool,
    #[arg(
        long,
        default_value = "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.bin"
    )]
    bundle: PathBuf,
    #[arg(
        long,
        default_value = "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.json"
    )]
    manifest: PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    if !args.write && !args.check {
        return Err("choose exactly one of --write or --check".into());
    }
    if args.bundle == args.manifest {
        return Err("bundle and manifest paths must differ".into());
    }
    let (bundle, manifest) = generate_r0_bundle()?;
    let bundle_bytes = encode_r0_bundle(&bundle)?;
    let manifest_bytes = r0_manifest_json(&manifest)?;
    if args.write {
        write_pair(&args.bundle, &bundle_bytes, &args.manifest, &manifest_bytes)?;
        println!(
            "wrote {} R0 coordinates to {} and {}",
            bundle.coordinates.len(),
            args.bundle.display(),
            args.manifest.display()
        );
    } else {
        check_pair(&args.bundle, &bundle_bytes, &args.manifest, &manifest_bytes)?;
        println!("windowed R0 corpus is byte-stable");
    }
    Ok(())
}

trait FileOps {
    fn exists(&self, path: &Path) -> std::io::Result<bool>;
    fn read(&self, path: &Path) -> std::io::Result<Vec<u8>>;
    fn stage(&self, path: &Path, bytes: &[u8], label: &str) -> std::io::Result<PathBuf>;
    fn replace(&self, source: &Path, destination: &Path) -> std::io::Result<()>;
    fn remove(&self, path: &Path) -> std::io::Result<()>;
}

struct StdFileOps;

impl FileOps for StdFileOps {
    fn exists(&self, path: &Path) -> std::io::Result<bool> {
        path.try_exists()
    }

    fn read(&self, path: &Path) -> std::io::Result<Vec<u8>> {
        fs::read(path)
    }

    fn stage(&self, path: &Path, bytes: &[u8], label: &str) -> std::io::Result<PathBuf> {
        write_temporary(path, bytes, label)
    }

    fn replace(&self, source: &Path, destination: &Path) -> std::io::Result<()> {
        fs::rename(source, destination)
    }

    fn remove(&self, path: &Path) -> std::io::Result<()> {
        fs::remove_file(path)
    }
}

#[derive(Debug)]
enum PublishError {
    Io {
        operation: &'static str,
        path: PathBuf,
        error: std::io::Error,
    },
    OneSidedPair {
        bundle: PathBuf,
        bundle_exists: bool,
        manifest: PathBuf,
        manifest_exists: bool,
    },
    MissingPair {
        bundle: PathBuf,
        manifest: PathBuf,
    },
    ContentMismatch {
        bundle: PathBuf,
        manifest: PathBuf,
    },
    Rollback {
        replacement: Box<Self>,
        rollback: Box<Self>,
    },
    Cleanup {
        primary: Box<Self>,
        cleanup: Vec<Self>,
    },
}

impl PublishError {
    fn io(operation: &'static str, path: &Path, error: std::io::Error) -> Self {
        Self::Io {
            operation,
            path: path.to_path_buf(),
            error,
        }
    }
}

impl core::fmt::Display for PublishError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Io {
                operation,
                path,
                error,
            } => write!(formatter, "{operation} {}: {error}", path.display()),
            Self::OneSidedPair {
                bundle,
                bundle_exists,
                manifest,
                manifest_exists,
            } => write!(
                formatter,
                "refusing one-sided corpus pair: {} exists={}, {} exists={}",
                bundle.display(),
                bundle_exists,
                manifest.display(),
                manifest_exists,
            ),
            Self::MissingPair { bundle, manifest } => write!(
                formatter,
                "both corpus outputs must exist for --check: {} and {}",
                bundle.display(),
                manifest.display(),
            ),
            Self::ContentMismatch { bundle, manifest } => write!(
                formatter,
                "{} or {} differs from deterministic regeneration",
                bundle.display(),
                manifest.display(),
            ),
            Self::Rollback {
                replacement,
                rollback,
            } => write!(
                formatter,
                "replacement failed ({replacement}); rollback also failed ({rollback})",
            ),
            Self::Cleanup { primary, cleanup } => write!(
                formatter,
                "{primary}; temporary cleanup also failed: {cleanup:?}",
            ),
        }
    }
}

impl std::error::Error for PublishError {}

fn check_pair(
    bundle_path: &Path,
    expected_bundle: &[u8],
    manifest_path: &Path,
    expected_manifest: &[u8],
) -> Result<(), PublishError> {
    check_pair_with_ops(
        &StdFileOps,
        bundle_path,
        expected_bundle,
        manifest_path,
        expected_manifest,
    )
}

fn check_pair_with_ops(
    ops: &impl FileOps,
    bundle_path: &Path,
    expected_bundle: &[u8],
    manifest_path: &Path,
    expected_manifest: &[u8],
) -> Result<(), PublishError> {
    let (bundle_exists, _) = pair_state_with_ops(ops, bundle_path, manifest_path)?;
    if !bundle_exists {
        return Err(PublishError::MissingPair {
            bundle: bundle_path.to_path_buf(),
            manifest: manifest_path.to_path_buf(),
        });
    }
    let bundle = ops
        .read(bundle_path)
        .map_err(|error| PublishError::io("read bundle", bundle_path, error))?;
    let manifest = ops
        .read(manifest_path)
        .map_err(|error| PublishError::io("read manifest", manifest_path, error))?;
    if bundle != expected_bundle || manifest != expected_manifest {
        return Err(PublishError::ContentMismatch {
            bundle: bundle_path.to_path_buf(),
            manifest: manifest_path.to_path_buf(),
        });
    }
    Ok(())
}

fn write_pair(
    bundle_path: &Path,
    bundle: &[u8],
    manifest_path: &Path,
    manifest: &[u8],
) -> Result<(), PublishError> {
    write_pair_with_ops(&StdFileOps, bundle_path, bundle, manifest_path, manifest)
}

fn write_pair_with_ops(
    ops: &impl FileOps,
    bundle_path: &Path,
    bundle: &[u8],
    manifest_path: &Path,
    manifest: &[u8],
) -> Result<(), PublishError> {
    let (bundle_exists, _) = pair_state_with_ops(ops, bundle_path, manifest_path)?;
    let old_bundle = bundle_exists
        .then(|| ops.read(bundle_path))
        .transpose()
        .map_err(|error| PublishError::io("read existing bundle", bundle_path, error))?;
    let bundle_temp = ops
        .stage(bundle_path, bundle, "bundle")
        .map_err(|error| PublishError::io("stage bundle", bundle_path, error))?;
    let manifest_temp = match ops.stage(manifest_path, manifest, "manifest") {
        Ok(path) => path,
        Err(error) => {
            return finish_with_cleanup(
                ops,
                PublishError::io("stage manifest", manifest_path, error),
                &[bundle_temp],
            );
        }
    };

    if let Err(error) = ops.replace(&bundle_temp, bundle_path) {
        return finish_with_cleanup(
            ops,
            PublishError::io("replace bundle", bundle_path, error),
            &[bundle_temp, manifest_temp],
        );
    }
    if let Err(error) = ops.replace(&manifest_temp, manifest_path) {
        let replacement = PublishError::io("replace manifest", manifest_path, error);
        let primary = match rollback_bundle(ops, bundle_path, old_bundle.as_deref()) {
            Ok(()) => replacement,
            Err(rollback) => PublishError::Rollback {
                replacement: Box::new(replacement),
                rollback: Box::new(rollback),
            },
        };
        return finish_with_cleanup(ops, primary, &[manifest_temp]);
    }
    Ok(())
}

fn finish_with_cleanup(
    ops: &impl FileOps,
    primary: PublishError,
    temporary_paths: &[PathBuf],
) -> Result<(), PublishError> {
    let cleanup = temporary_paths
        .iter()
        .filter_map(|path| {
            ops.remove(path)
                .err()
                .map(|error| PublishError::io("remove temporary", path, error))
        })
        .collect::<Vec<_>>();
    if cleanup.is_empty() {
        Err(primary)
    } else {
        Err(PublishError::Cleanup {
            primary: Box::new(primary),
            cleanup,
        })
    }
}

fn rollback_bundle(
    ops: &impl FileOps,
    bundle_path: &Path,
    original: Option<&[u8]>,
) -> Result<(), PublishError> {
    match original {
        Some(bytes) => {
            let temporary = ops
                .stage(bundle_path, bytes, "rollback")
                .map_err(|error| PublishError::io("stage rollback", bundle_path, error))?;
            if let Err(error) = ops.replace(&temporary, bundle_path) {
                return finish_with_cleanup(
                    ops,
                    PublishError::io("replace rollback", bundle_path, error),
                    &[temporary],
                );
            }
            Ok(())
        }
        None => ops
            .remove(bundle_path)
            .map_err(|error| PublishError::io("remove newly published bundle", bundle_path, error)),
    }
}

fn pair_state_with_ops(
    ops: &impl FileOps,
    bundle_path: &Path,
    manifest_path: &Path,
) -> Result<(bool, bool), PublishError> {
    let bundle_exists = ops
        .exists(bundle_path)
        .map_err(|error| PublishError::io("inspect bundle", bundle_path, error))?;
    let manifest_exists = ops
        .exists(manifest_path)
        .map_err(|error| PublishError::io("inspect manifest", manifest_path, error))?;
    if bundle_exists != manifest_exists {
        return Err(PublishError::OneSidedPair {
            bundle: bundle_path.to_path_buf(),
            bundle_exists,
            manifest: manifest_path.to_path_buf(),
            manifest_exists,
        });
    }
    Ok((bundle_exists, manifest_exists))
}

fn write_temporary(path: &Path, bytes: &[u8], label: &str) -> std::io::Result<PathBuf> {
    let parent = path
        .parent()
        .filter(|parent| parent.is_dir())
        .ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("output parent does not exist for {}", path.display()),
            )
        })?;
    let file_name = path
        .file_name()
        .ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("output path has no file name: {}", path.display()),
            )
        })?
        .to_string_lossy();
    let temporary = parent.join(format!(".{file_name}.{}.{}.tmp", std::process::id(), label));
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&temporary)?;
    if let Err(error) = file.write_all(bytes).and_then(|()| file.sync_all()) {
        drop(file);
        return match fs::remove_file(&temporary) {
            Ok(()) => Err(error),
            Err(cleanup) => Err(std::io::Error::new(
                error.kind(),
                format!(
                    "{error}; failed to remove {}: {cleanup}",
                    temporary.display()
                ),
            )),
        };
    }
    Ok(temporary)
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::io;

    use super::*;

    const OLD_BUNDLE: &[u8] = b"old bundle";
    const OLD_MANIFEST: &[u8] = b"old manifest";
    const NEW_BUNDLE: &[u8] = b"new bundle";
    const NEW_MANIFEST: &[u8] = b"new manifest";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Fault {
        StageManifest,
        ReplaceBundle,
        ReplaceManifest,
        ReplaceRollback,
        CleanupBundle,
    }

    struct FakeOps {
        files: RefCell<BTreeMap<PathBuf, Vec<u8>>>,
        events: RefCell<Vec<String>>,
        faults: Vec<Fault>,
    }

    impl FakeOps {
        fn existing(faults: &[Fault]) -> Self {
            let (bundle, manifest) = paths();
            Self {
                files: RefCell::new(BTreeMap::from([
                    (bundle, OLD_BUNDLE.to_vec()),
                    (manifest, OLD_MANIFEST.to_vec()),
                ])),
                events: RefCell::new(Vec::new()),
                faults: faults.to_vec(),
            }
        }

        fn one_sided() -> Self {
            let (bundle, _) = paths();
            Self {
                files: RefCell::new(BTreeMap::from([(bundle, OLD_BUNDLE.to_vec())])),
                events: RefCell::new(Vec::new()),
                faults: Vec::new(),
            }
        }

        fn file(&self, path: &Path) -> Option<Vec<u8>> {
            self.files.borrow().get(path).cloned()
        }

        fn staged(&self, path: &Path, label: &str) -> PathBuf {
            PathBuf::from(format!("{}.{}.tmp", path.display(), label))
        }

        fn has_fault(&self, fault: Fault) -> bool {
            self.faults.contains(&fault)
        }

        fn error(operation: &str) -> io::Error {
            io::Error::other(format!("injected {operation} failure"))
        }
    }

    impl FileOps for FakeOps {
        fn exists(&self, path: &Path) -> io::Result<bool> {
            Ok(self.files.borrow().contains_key(path))
        }

        fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
            self.file(path)
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, path.display().to_string()))
        }

        fn stage(&self, path: &Path, bytes: &[u8], label: &str) -> io::Result<PathBuf> {
            self.events.borrow_mut().push(format!("stage:{label}"));
            if label == "manifest" && self.has_fault(Fault::StageManifest) {
                return Err(Self::error("manifest staging"));
            }
            let temporary = self.staged(path, label);
            self.files
                .borrow_mut()
                .insert(temporary.clone(), bytes.to_vec());
            Ok(temporary)
        }

        fn replace(&self, source: &Path, destination: &Path) -> io::Result<()> {
            let (bundle, manifest) = paths();
            let label = source.to_string_lossy();
            self.events.borrow_mut().push(format!(
                "replace:{}",
                if destination == bundle {
                    "bundle"
                } else {
                    "manifest"
                }
            ));
            if destination == bundle
                && label.ends_with(".bundle.tmp")
                && self.has_fault(Fault::ReplaceBundle)
            {
                return Err(Self::error("bundle replacement"));
            }
            if destination == manifest && self.has_fault(Fault::ReplaceManifest) {
                return Err(Self::error("manifest replacement"));
            }
            if destination == bundle
                && label.ends_with(".rollback.tmp")
                && self.has_fault(Fault::ReplaceRollback)
            {
                return Err(Self::error("rollback replacement"));
            }
            let bytes = self.files.borrow_mut().remove(source).ok_or_else(|| {
                io::Error::new(io::ErrorKind::NotFound, source.display().to_string())
            })?;
            self.files
                .borrow_mut()
                .insert(destination.to_path_buf(), bytes);
            Ok(())
        }

        fn remove(&self, path: &Path) -> io::Result<()> {
            self.events
                .borrow_mut()
                .push(format!("remove:{}", path.display()));
            if path.to_string_lossy().ends_with(".bundle.tmp")
                && self.has_fault(Fault::CleanupBundle)
            {
                return Err(Self::error("bundle temporary cleanup"));
            }
            self.files.borrow_mut().remove(path);
            Ok(())
        }
    }

    fn paths() -> (PathBuf, PathBuf) {
        (
            PathBuf::from("/bundle/windowed_r0.bin"),
            PathBuf::from("/manifest/windowed_r0.json"),
        )
    }

    #[test]
    fn cpu_r0_writer_stages_both_files_before_the_first_replacement() {
        let ops = FakeOps::existing(&[]);
        let (bundle, manifest) = paths();

        write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).unwrap();

        assert_eq!(ops.file(&bundle), Some(NEW_BUNDLE.to_vec()));
        assert_eq!(ops.file(&manifest), Some(NEW_MANIFEST.to_vec()));
        assert_eq!(
            &ops.events.borrow()[..3],
            ["stage:bundle", "stage:manifest", "replace:bundle"]
        );
    }

    #[test]
    fn cpu_r0_writer_rejects_a_one_sided_preexisting_pair() {
        let ops = FakeOps::one_sided();
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());
        assert!(ops.events.borrow().is_empty());
    }

    #[test]
    fn cpu_r0_writer_cleans_the_bundle_temp_when_manifest_staging_fails() {
        let ops = FakeOps::existing(&[Fault::StageManifest]);
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());

        assert_eq!(ops.file(&bundle), Some(OLD_BUNDLE.to_vec()));
        assert_eq!(ops.file(&manifest), Some(OLD_MANIFEST.to_vec()));
        assert_eq!(ops.file(&ops.staged(&bundle, "bundle")), None);
    }

    #[test]
    fn cpu_r0_writer_cleans_both_temps_when_the_first_replacement_fails() {
        let ops = FakeOps::existing(&[Fault::ReplaceBundle]);
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());

        assert_eq!(ops.file(&bundle), Some(OLD_BUNDLE.to_vec()));
        assert_eq!(ops.file(&manifest), Some(OLD_MANIFEST.to_vec()));
        assert_eq!(ops.file(&ops.staged(&bundle, "bundle")), None);
        assert_eq!(ops.file(&ops.staged(&manifest, "manifest")), None);
    }

    #[test]
    fn cpu_r0_writer_restores_the_old_bundle_when_the_second_replacement_fails() {
        let ops = FakeOps::existing(&[Fault::ReplaceManifest]);
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());

        assert_eq!(ops.file(&bundle), Some(OLD_BUNDLE.to_vec()));
        assert_eq!(ops.file(&manifest), Some(OLD_MANIFEST.to_vec()));
        assert_eq!(ops.file(&ops.staged(&manifest, "manifest")), None);
    }

    #[test]
    fn cpu_r0_writer_reports_rollback_failure_and_check_rejects_the_mixed_pair() {
        let ops = FakeOps::existing(&[Fault::ReplaceManifest, Fault::ReplaceRollback]);
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());

        assert_eq!(ops.file(&bundle), Some(NEW_BUNDLE.to_vec()));
        assert_eq!(ops.file(&manifest), Some(OLD_MANIFEST.to_vec()));
        assert!(check_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());
    }

    #[test]
    fn cpu_r0_writer_reports_a_temporary_cleanup_failure_without_hiding_the_primary_failure() {
        let ops = FakeOps::existing(&[Fault::ReplaceBundle, Fault::CleanupBundle]);
        let (bundle, manifest) = paths();

        assert!(write_pair_with_ops(&ops, &bundle, NEW_BUNDLE, &manifest, NEW_MANIFEST).is_err());

        assert_eq!(ops.file(&manifest), Some(OLD_MANIFEST.to_vec()));
        assert_eq!(ops.file(&ops.staged(&manifest, "manifest")), None);
        assert_eq!(
            ops.file(&ops.staged(&bundle, "bundle")),
            Some(NEW_BUNDLE.to_vec())
        );
    }
}
