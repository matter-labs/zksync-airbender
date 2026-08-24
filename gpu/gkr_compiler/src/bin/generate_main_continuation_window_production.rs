//! Render or verify the committed main-continuation kernel bank.
//!
//! `--probe-write` accepts a strict candidate launch-bound bank and writes it
//! to the normal generated paths. A later normal `--write` always restores the
//! authoritative bank.

use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use gpu_gkr_compiler::backward::main_continuation_window_manifest::{
    main_continuation_window_generated_artifacts,
    main_continuation_window_generated_artifacts_for_bank,
    parse_main_continuation_window_candidate_bank, repo_root,
    validate_main_continuation_window_generated_tree,
};

enum Mode {
    Write,
    Check,
    ProbeWrite(String),
}

fn usage(program: &str) -> String {
    format!("usage: {program} --write | --check | --probe-write <candidate-bank.json>")
}

fn parse_mode(program: &str, args: impl IntoIterator<Item = String>) -> Result<Mode, String> {
    let mut args = args.into_iter();
    match (args.next().as_deref(), args.next(), args.next()) {
        (Some("--write"), None, None) => Ok(Mode::Write),
        (Some("--check"), None, None) => Ok(Mode::Check),
        (Some("--probe-write"), Some(path), None) => Ok(Mode::ProbeWrite(path)),
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
            let artifacts = main_continuation_window_generated_artifacts()?;
            write_artifacts(&root, &artifacts)
        }
        Mode::Check => {
            let artifacts = main_continuation_window_generated_artifacts()?;
            check_artifacts(&root, &artifacts)
        }
        Mode::ProbeWrite(candidate_path) => {
            let json = fs::read_to_string(&candidate_path)
                .map_err(|error| format!("{candidate_path}: {error}"))?;
            let bank = parse_main_continuation_window_candidate_bank(&json)?;
            let artifacts = main_continuation_window_generated_artifacts_for_bank(&bank)?;
            write_artifacts(&root, &artifacts)?;
            println!("wrote non-authoritative probe bank from {candidate_path}");
            Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_main_continuation_window_manifest_generator_cli_is_strict() {
        assert!(matches!(
            parse_mode("generate", ["--write".to_owned()]),
            Ok(Mode::Write)
        ));
        assert!(matches!(
            parse_mode("generate", ["--check".to_owned()]),
            Ok(Mode::Check)
        ));
        assert!(matches!(
            parse_mode(
                "generate",
                ["--probe-write".to_owned(), "candidate.json".to_owned()]
            ),
            Ok(Mode::ProbeWrite(path)) if path == "candidate.json"
        ));
        for invalid in [
            vec![],
            vec!["--probe-write".to_owned()],
            vec!["--check".to_owned(), "extra".to_owned()],
            vec!["--unknown".to_owned()],
        ] {
            assert!(parse_mode("generate", invalid).is_err());
        }
    }
}
