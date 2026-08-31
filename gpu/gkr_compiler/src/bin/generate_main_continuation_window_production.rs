//! Render or verify the committed main-continuation kernel bank.

use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use gpu_gkr_compiler::backward::main_continuation_window_manifest::{
    main_continuation_window_generated_artifacts, repo_root,
    validate_main_continuation_window_generated_tree,
};

enum Mode {
    Write,
    Check,
}

fn usage(program: &str) -> String {
    format!("usage: {program} --write | --check")
}

fn parse_mode(program: &str, args: impl IntoIterator<Item = String>) -> Result<Mode, String> {
    let mut args = args.into_iter();
    match (args.next().as_deref(), args.next(), args.next()) {
        (Some("--write"), None, None) => Ok(Mode::Write),
        (Some("--check"), None, None) => Ok(Mode::Check),
        _ => Err(usage(program)),
    }
}

fn write_artifacts(root: &Path, artifacts: &[(String, String)]) -> Result<(), String> {
    for (relative, rendered) in artifacts {
        let path = root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| format!("{relative}: {error}"))?;
        }
        fs::write(&path, rendered).map_err(|error| format!("{relative}: {error}"))?;
        println!("wrote {relative}");
    }
    validate_main_continuation_window_generated_tree(root)
}

fn check_artifacts(root: &Path, artifacts: &[(String, String)]) -> Result<(), String> {
    let mut stale = Vec::new();
    for (relative, rendered) in artifacts {
        match fs::read_to_string(root.join(relative)) {
            Ok(committed) if committed == *rendered => {}
            Ok(_) => stale.push(format!("{relative}: contents differ")),
            Err(error) => stale.push(format!("{relative}: {error}")),
        }
    }
    if let Err(error) = validate_main_continuation_window_generated_tree(root) {
        stale.push(error);
    }
    if stale.is_empty() {
        println!(
            "{} main-continuation-window artifacts are current",
            artifacts.len()
        );
        return Ok(());
    }
    Err(format!(
        "{}\nrerun with --write and commit the result",
        stale.join("\n")
    ))
}

fn run() -> Result<(), String> {
    let mut args = env::args();
    let program = args
        .next()
        .unwrap_or_else(|| "generate_main_continuation_window_production".to_owned());
    let mode = parse_mode(&program, args)?;
    let root = repo_root();
    match mode {
        Mode::Write => {
            let artifacts = main_continuation_window_generated_artifacts();
            write_artifacts(&root, &artifacts)
        }
        Mode::Check => {
            let artifacts = main_continuation_window_generated_artifacts();
            check_artifacts(&root, &artifacts)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
