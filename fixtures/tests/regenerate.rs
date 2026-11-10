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
    Command::new("bash")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("regenerate.sh"))
        .args(arguments)
        .env("AB_TEST_ARTIFACT_ROOT", root)
        .env("FIXTURE_CLI", root.join("cli"))
        .env("FIXTURE_CODEC", root.join("codec"))
        .env("FIXTURE_CANONICAL_PRODUCER", root.join("producer"))
        .env("TMPDIR", root)
        .env("CI", "true")
        .output()
        .unwrap()
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
proof= output_dir= output_file=
while (($#)); do
  case $1 in
    --proof) proof=$2 ;;
    --output-dir) output_dir=$2 ;;
    --output-file) output_file=$2 ;;
  esac
  shift 2
done
if [[ $action == verify ]]; then [[ -f $proof ]]; exit; fi
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
        "#!/bin/sh\ntest -n \"$FIXTURE_CHAIN_ROOT\"\ntest -n \"$SMOKE_OUTPUT_DIR\"\n",
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
    for stage in ["base_unified", "unrolled"] {
        let result = run(
            &root,
            &[
                "--check",
                "--mode",
                "pessimistic_conjecture",
                "--stage",
                stage,
            ],
        );
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
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
