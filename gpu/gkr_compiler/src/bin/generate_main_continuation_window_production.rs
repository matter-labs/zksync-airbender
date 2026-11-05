//! Render or verify the committed main-continuation kernel bank.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::proth120::Proth120;
use gpu_gkr_compiler::backward::main_continuation_window_manifest::{
    main_continuation_window_generated_artifacts, pr_main_continuation_masks,
    pr_main_continuation_window_generated_artifacts, repo_root,
    validate_main_continuation_window_generated_tree,
    validate_pr_main_continuation_window_generated_tree, PR_MAIN_CONTINUATION_MASKS,
};

enum Mode {
    Write,
    Check,
}

struct Proth120Args {
    layout: PathBuf,
    output_root: Option<PathBuf>,
}

fn usage(program: &str) -> String {
    format!(
        "usage: {program} --write | --check\n       {program} --field proth120 --layout <layout-json> [--output-root <dir>] --write | --check"
    )
}

fn parse_args(
    program: &str,
    args: impl IntoIterator<Item = String>,
) -> Result<(Mode, Option<Proth120Args>), String> {
    let mut mode = None;
    let mut field = None;
    let mut layout = None;
    let mut output_root = None;
    let mut args = args.into_iter();
    while let Some(flag) = args.next() {
        let value = |args: &mut dyn Iterator<Item = String>| {
            args.next()
                .ok_or_else(|| format!("{flag} needs a value\n{}", usage(program)))
        };
        match flag.as_str() {
            "--write" | "--check" if mode.is_none() => {
                mode = Some(if flag == "--write" {
                    Mode::Write
                } else {
                    Mode::Check
                })
            }
            "--field" if field.is_none() => field = Some(value(&mut args)?),
            "--layout" if layout.is_none() => layout = Some(PathBuf::from(value(&mut args)?)),
            "--output-root" if output_root.is_none() => {
                output_root = Some(PathBuf::from(value(&mut args)?))
            }
            _ => return Err(usage(program)),
        }
    }
    let mode = mode.ok_or_else(|| usage(program))?;
    match (field.as_deref(), layout) {
        (None, None) if output_root.is_none() => Ok((mode, None)),
        (Some("proth120"), Some(layout)) => Ok((
            mode,
            Some(Proth120Args {
                layout,
                output_root,
            }),
        )),
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
    Ok(())
}

fn check_artifacts(
    artifacts: &[(String, String)],
    root: &Path,
    tree: Result<(), String>,
) -> Result<(), String> {
    let mut stale = Vec::new();
    for (relative, rendered) in artifacts {
        match fs::read_to_string(root.join(relative)) {
            Ok(committed) if committed == *rendered => {}
            Ok(_) => stale.push(format!("{relative}: contents differ")),
            Err(error) => stale.push(format!("{relative}: {error}")),
        }
    }
    if let Err(error) = tree {
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
    let (mode, proth120) = parse_args(&program, args)?;
    let Some(proth120) = proth120 else {
        let root = repo_root();
        let artifacts = main_continuation_window_generated_artifacts();
        return match mode {
            Mode::Write => {
                write_artifacts(&root, &artifacts)?;
                validate_main_continuation_window_generated_tree(&root)
            }
            Mode::Check => check_artifacts(
                &artifacts,
                &root,
                validate_main_continuation_window_generated_tree(&root),
            ),
        };
    };
    let bytes = fs::read(&proth120.layout)
        .map_err(|error| format!("{}: {error}", proth120.layout.display()))?;
    let layout: GKRCircuitArtifact<Proth120> =
        serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let masks = pr_main_continuation_masks(&layout)?;
    if masks != PR_MAIN_CONTINUATION_MASKS {
        return Err(format!(
            "lowered Proth120 masks {masks:#04x?} differ from PR_MAIN_CONTINUATION_MASKS {PR_MAIN_CONTINUATION_MASKS:#04x?}; update the constant"
        ));
    }
    let root = proth120.output_root.unwrap_or_else(repo_root);
    let artifacts = pr_main_continuation_window_generated_artifacts(&masks);
    match mode {
        Mode::Write => {
            write_artifacts(&root, &artifacts)?;
            validate_pr_main_continuation_window_generated_tree(&root, &masks)
        }
        Mode::Check => check_artifacts(
            &artifacts,
            &root,
            validate_pr_main_continuation_window_generated_tree(&root, &masks),
        ),
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
