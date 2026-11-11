#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::{Command, Output};

fn executable(path: &Path, body: &str) {
    fs::write(path, body).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

fn run(root: &Path, arguments: &[&str]) -> Output {
    run_with_backend(root, arguments, None)
}

fn run_with_backend(root: &Path, arguments: &[&str], backend: Option<&str>) -> Output {
    command(root, arguments, backend).output().unwrap()
}

fn command(root: &Path, arguments: &[&str], backend: Option<&str>) -> Command {
    let mut command = Command::new("bash");
    command
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("regenerate.sh"))
        .args(arguments)
        .env("AB_TEST_ARTIFACT_ROOT", root)
        .env("FIXTURE_CLI", root.join("cli"))
        .env("FIXTURE_CODEC", root.join("codec"))
        .env("FIXTURE_CANONICAL_PRODUCER", root.join("producer"))
        .env("TMPDIR", root)
        .env_remove("FIXTURE_BACKEND")
        .env_remove("EXPECTED_FIXTURE_BACKEND")
        .env_remove("FIXTURE_TRUSTED_PARAMS");
    if let Some(backend) = backend {
        command
            .env("FIXTURE_BACKEND", backend)
            .env("EXPECTED_FIXTURE_BACKEND", backend);
    }
    command
}

#[test]
fn checks_read_committed_parents_and_compare_only_their_stage() {
    let root = std::env::temp_dir().join(format!("proof-fixture-recipe-{}", std::process::id()));
    fs::create_dir_all(root.join("fixtures/chains/pessimistic_conjecture")).unwrap();
    fs::create_dir_all(root.join(".github/scripts")).unwrap();
    executable(
        &root.join("cli"),
        r##"#!/usr/bin/env bash
set -euo pipefail
action=$1; shift
proof= output_dir= output_file= backend= trusted= output=
while (($#)); do
  case $1 in
    --proof) proof=$2 ;;
    --trusted-params) trusted=$2 ;;
    --output) output=$2 ;;
    --output-dir) output_dir=$2 ;;
    --output-file) output_file=$2 ;;
    --backend) backend=$2 ;;
    --gpu-memory-preset) exit 1 ;;
  esac
  shift 2
done
if [[ $action == trusted-params ]]; then printf params >"$output"; exit; fi
if [[ $action == verify ]]; then
  [[ -f $proof ]]
  if [[ -n ${FIXTURE_TRUSTED_PARAMS:-} ]]; then [[ -f $trusted ]]; else [[ -z $trusted ]]; fi
  exit
fi
[[ $backend == "${EXPECTED_FIXTURE_BACKEND:-cpu}" ]]
if [[ $action == continue-proof ]]; then
  [[ $proof == "$AB_TEST_ARTIFACT_ROOT/fixtures/chains/pessimistic_conjecture/base.json.zlib" ||
     $proof == "$AB_TEST_ARTIFACT_ROOT/fixtures/chains/pessimistic_conjecture/unrolled.json.zlib" ]]
fi
mkdir -p "$output_dir"
printf '%s' "$output_file" >"$output_dir/$output_file"
"##,
    );
    executable(&root.join("codec"), "#!/bin/sh\ntest -f \"$2\"\n");
    executable(
        &root.join("producer"),
        "#!/bin/sh\necho 'test result: ok. 0 passed; 0 failed'\n",
    );
    executable(
        &root.join(".github/scripts/soundness_mode_smoke.sh"),
        "#!/bin/sh\ntest -n \"$FIXTURE_CHAIN_ROOT\"\ntest -n \"$SMOKE_OUTPUT_DIR\"\ntest \"$3\" = cpu\n",
    );
    for chain in proof_fixtures::CHAINS {
        let name = format!("{chain}.json.zlib");
        fs::write(
            root.join("fixtures/chains/pessimistic_conjecture")
                .join(&name),
            &name,
        )
        .unwrap();
    }
    for backend in [None, Some("cpu"), Some("gpu")] {
        for stage in ["base_unified", "unrolled"] {
            let result = run_with_backend(
                &root,
                &[
                    "--check",
                    "--mode",
                    "pessimistic_conjecture",
                    "--stage",
                    stage,
                ],
                backend,
            );
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
    }
    let trusted_params = root.join("trusted-params");
    let result = command(
        &root,
        &[
            "--check",
            "--mode",
            "pessimistic_conjecture",
            "--stage",
            "base_unified",
        ],
        None,
    )
    .env("FIXTURE_TRUSTED_PARAMS", &trusted_params)
    .output()
    .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(trusted_params
        .join("pessimistic-conjecture-trusted-params.json")
        .is_file());
    assert!(!trusted_params
        .join("ethproofs-soundcalc-trusted-params.json")
        .exists());
    for arguments in [vec!["--check"], vec!["--check", "--stage", "circuits"]] {
        let result = run_with_backend(&root, &arguments, Some("gpu"));
        assert!(!result.status.success());
        let error = String::from_utf8_lossy(&result.stderr);
        assert!(error.contains("FIXTURE_BACKEND=gpu"), "{error}");
        assert!(error.contains("circuits"), "{error}");
    }
    let result = run_with_backend(&root, &["--check", "--stage", "unrolled"], Some("invalid"));
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("unknown FIXTURE_BACKEND: invalid"));
    // A check owns only its stage; an unrelated stale artifact is not compared.
    let unified = root.join("fixtures/chains/pessimistic_conjecture/unified.json.zlib");
    fs::write(&unified, "stale").unwrap();
    assert!(run(
        &root,
        &[
            "--check",
            "--mode",
            "pessimistic_conjecture",
            "--stage",
            "unrolled"
        ]
    )
    .status
    .success());
    assert!(!run(
        &root,
        &[
            "--check",
            "--mode",
            "pessimistic_conjecture",
            "--stage",
            "base_unified"
        ]
    )
    .status
    .success());
    assert!(!run(
        &root,
        &["--mode", "pessimistic_conjecture", "--stage", "unrolled"]
    )
    .status
    .success());
    assert!(!run(
        &root,
        &["--mode", "pessimistic_conjecture", "--stage", "circuits"]
    )
    .status
    .success());
    fs::remove_dir_all(root).unwrap();
}
