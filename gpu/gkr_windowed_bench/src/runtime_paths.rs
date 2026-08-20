use std::path::{Path, PathBuf};
use std::sync::OnceLock;

static REPOSITORY_ROOT: OnceLock<PathBuf> = OnceLock::new();

fn validate_repository_root(path: &Path) -> Result<PathBuf, String> {
    let path = path
        .canonicalize()
        .map_err(|error| format!("resolve repository root {}: {error}", path.display()))?;
    if !path.join("Cargo.toml").is_file()
        || !path.join("gpu/gkr_windowed_bench/Cargo.toml").is_file()
    {
        return Err(format!("invalid repository root {}", path.display()));
    }
    Ok(path)
}

fn discover_repository_root(cwd: &Path, executable: &Path) -> Result<PathBuf, String> {
    for start in [Some(cwd), executable.parent()].into_iter().flatten() {
        for candidate in start.ancestors() {
            if candidate.join("Cargo.toml").is_file()
                && candidate
                    .join("gpu/gkr_windowed_bench/Cargo.toml")
                    .is_file()
            {
                return validate_repository_root(candidate);
            }
        }
    }
    Err(format!(
        "discover repository root from cwd={} or executable={}",
        cwd.display(),
        executable.display()
    ))
}

pub fn set_repository_root(path: &Path) -> Result<(), String> {
    let path = validate_repository_root(path)?;
    if let Some(existing) = REPOSITORY_ROOT.get() {
        return (existing == &path)
            .then_some(())
            .ok_or_else(|| format!("repository root already bound to {}", existing.display()));
    }
    REPOSITORY_ROOT
        .set(path)
        .map_err(|path| format!("repository root already bound before {}", path.display()))
}

pub fn repository_root() -> PathBuf {
    REPOSITORY_ROOT
        .get_or_init(|| {
            let cwd = std::env::current_dir().expect("read current directory");
            let executable = std::env::current_exe().expect("read current executable");
            discover_repository_root(&cwd, &executable)
                .unwrap_or_else(|error| panic!("{error}; bind a runtime repository root first"))
        })
        .clone()
}

pub fn crate_root() -> PathBuf {
    repository_root().join("gpu/gkr_windowed_bench")
}

pub fn compiled_circuits_directory() -> PathBuf {
    repository_root().join("cs/compiled_circuits")
}

#[cfg(test)]
mod tests {
    use super::discover_repository_root;

    #[test]
    fn cpu_runtime_repository_discovery_uses_only_runtime_paths() {
        let fixture =
            std::env::temp_dir().join(format!("windowed-r0-runtime-paths-{}", std::process::id()));
        let executable = fixture.join("target/release/runner");
        std::fs::create_dir_all(fixture.join("gpu/gkr_windowed_bench")).unwrap();
        std::fs::create_dir_all(executable.parent().unwrap()).unwrap();
        std::fs::write(fixture.join("Cargo.toml"), "[workspace]\n").unwrap();
        std::fs::write(
            fixture.join("gpu/gkr_windowed_bench/Cargo.toml"),
            "[package]\nname='fixture'\nversion='0.0.0'\n",
        )
        .unwrap();
        assert_eq!(
            discover_repository_root(&fixture.join("nested/path"), &executable).unwrap(),
            fixture
        );
        std::fs::remove_dir_all(fixture).unwrap();
    }
}
