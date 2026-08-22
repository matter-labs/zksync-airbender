//! Regenerate (or verify) the committed windowed-R0 production artifacts: the
//! eleven generated CUDA translation units, their manifest header, and the Rust
//! FFI registry.
//!
//! ```text
//! cargo run -p gpu_gkr_compiler --features codegen \
//!     --bin generate_windowed_r0_production -- --write
//! cargo run -p gpu_gkr_compiler --features codegen \
//!     --bin generate_windowed_r0_production -- --check
//! ```
//!
//! `--check` is the drift guard's command-line form; the same comparison runs as
//! `cpu_committed_generated_artifacts_are_current`.

use std::env;
use std::fs;
use std::process::ExitCode;

use gpu_gkr_compiler::backward::window_manifest::{repo_root, windowed_r0_generated_artifacts};

fn usage(program: &str) -> String {
    format!("usage: {program} --write | --check")
}

fn main() -> ExitCode {
    let mut args = env::args();
    let program = args.next().unwrap_or_else(|| "generate".to_owned());
    let mode = args.next();
    if args.next().is_some() {
        eprintln!("{}", usage(&program));
        return ExitCode::FAILURE;
    }
    let write = match mode.as_deref() {
        Some("--write") => true,
        Some("--check") => false,
        _ => {
            eprintln!("{}", usage(&program));
            return ExitCode::FAILURE;
        }
    };

    let artifacts = match windowed_r0_generated_artifacts() {
        Ok(artifacts) => artifacts,
        Err(error) => {
            eprintln!("dispatch manifest is invalid: {error}");
            return ExitCode::FAILURE;
        }
    };

    let root = repo_root();
    let mut stale = Vec::new();
    for (relative, rendered) in &artifacts {
        let path = root.join(relative);
        if write {
            if let Some(parent) = path.parent() {
                if let Err(error) = fs::create_dir_all(parent) {
                    eprintln!("{relative}: {error}");
                    return ExitCode::FAILURE;
                }
            }
            if let Err(error) = fs::write(&path, rendered) {
                eprintln!("{relative}: {error}");
                return ExitCode::FAILURE;
            }
            println!("wrote {relative}");
        } else {
            match fs::read_to_string(&path) {
                Ok(committed) if committed == *rendered => {}
                Ok(_) => stale.push(format!("{relative}: contents differ")),
                Err(error) => stale.push(format!("{relative}: {error}")),
            }
        }
    }

    if write {
        return ExitCode::SUCCESS;
    }
    if stale.is_empty() {
        println!("{} windowed R0 artifacts are current", artifacts.len());
        return ExitCode::SUCCESS;
    }
    for entry in stale {
        eprintln!("{entry}");
    }
    eprintln!("rerun with --write and commit the result");
    ExitCode::FAILURE
}
