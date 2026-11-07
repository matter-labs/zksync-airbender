#!/usr/bin/env python3
"""Reuse completed native qualification only for identical producer inputs.

The small receipt cache is independent of Cargo/Lean build caches. Missing or
invalid receipts require fresh native work. Full assurance, cold builds and
setup requalification always require fresh native work. No Lean gate is skipped.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

import check_setup_artifacts as setup
import check_gkr_translations as compiler
import check_native_evidence as evidence
import check_gkr_window_semantics as windows

REPO = setup.REPO
PREFIX = "formal_verification/lean/"
SCRIPTS = PREFIX + "scripts/"
FORCE_FLAGS = ("FV_FULL_ASSURANCE", "FV_COLD_BUILD", "FV_REQUALIFY_SETUPS")
CHECKS = ["12-native-generators", "16-complete-setups-and-dep-info",
          "33-compiler-payloads-and-provenance", "11-native-identities"]
# Include subprocess entry points as well as their local Python import closure.
# Workflow bytes pin commands, resource profiles, environment and this inventory.
ENTRY_POINTS = (
    "native_qualification.py", "check_setup_freshness.py", "generate.py",
    "export_gkr_translations.py", "check_compiler_export_bytes.py",
    "check_gkr_translations.py", "check_gkr_window_semantics.py",
    "qualify_native_memory.py", "bounded_fv.py",
    "test_setup_provenance.py", "test_gkr_translation_provenance.py",
)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     allow_nan=False).encode()).hexdigest()


def script_inputs(repo):
    """Conservatively include local imports, including imports inside functions."""
    directory = repo / SCRIPTS
    pending = [directory / name for name in ENTRY_POINTS]
    # The guard loads pool machinery through a package; include its whole code.
    pending.extend((directory / "compilation_pool").rglob("*.py"))
    found = set()
    while pending:
        path = pending.pop()
        relative = path.relative_to(repo).as_posix()
        if relative in found:
            continue
        found.add(relative)
        tree = ast.parse(path.read_text(), filename=relative)
        for node in ast.walk(tree):
            names = []
            if isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.module:
                names = [node.module]
            for name in names:
                candidate = directory.joinpath(*name.split(".")).with_suffix(".py")
                if candidate.is_file():
                    pending.append(candidate)
    return found


def fingerprint(repo=REPO):
    repo = Path(repo)
    # These check the complete current Rust source/include inventory, lock,
    # retained bytes, production identities and compiler inputs. Repinning a
    # manifest alone changes the fingerprint and cannot reuse old qualification.
    setup.check(repo)
    compiler.check(repo / PREFIX / "artifacts/compiler", repo=repo)
    evidence.check(repo)
    manifest = setup.read_json(repo / PREFIX / "artifacts/setup/manifest.json")
    paths = set(manifest["source_sha256"]) | script_inputs(repo)
    paths.update(compiler.COMPILER_INPUTS)
    paths.update(evidence.SOURCES | windows.SOURCES)
    paths.update(("Cargo.toml", "rust-toolchain.toml",
                  ".github/workflows/ci.yml", ".github/workflows/formal-verification.yml",
                  PREFIX + "lakefile.toml", setup.NATIVE_LOCK))
    for directory in ("artifacts/setup", "artifacts/compiler"):
        paths.update(path.relative_to(repo).as_posix()
                     for path in (repo / PREFIX / directory).rglob("*.json"))
    # Both cached compiler identities and no-cache generator outputs are inputs.
    paths.update(path.relative_to(repo).as_posix()
                 for path in (repo / "cs/compiled_circuits").glob("*gkr.json"))
    inputs = {name: setup.sha256(setup.checked_path(repo, name)) for name in sorted(paths)}
    environment = {key: value for key, value in os.environ.items()
                   if key in {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CC", "CXX", "AR",
                              "CFLAGS", "CXXFLAGS", "LDFLAGS", "RUSTC_WRAPPER",
                              "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN"}
                   or key.startswith("CARGO_PROFILE_")}
    runtime = {"system": platform.system(), "machine": platform.machine(),
               "python": platform.python_version(),
               "rustc": subprocess.check_output(["rustc", "--version", "--verbose"],
                                                cwd=repo, text=True).strip(),
               "cargo": subprocess.check_output(["cargo", "--version"],
                                                cwd=repo, text=True).strip(),
               "environment": environment}
    payload = {"schema": 1, "inputs": inputs, "runtime": runtime}
    return {**payload, "sha256": digest(payload)}


def reusable(receipt, current, environment):
    if any(environment.get(flag) == "true" for flag in FORCE_FLAGS):
        return False, "fresh native work requested by assurance/cold/requalification mode"
    if receipt is None:
        return False, "no retained native qualification receipt"
    if (receipt.get("schema") != 1 or receipt.get("fingerprint") != current["sha256"]
            or receipt.get("checks") != CHECKS
            or not re.fullmatch(r"[0-9a-f]{40}", str(receipt.get("commit", "")))
            or not re.fullmatch(r"[1-9][0-9]*", str(receipt.get("run_id", "")))
            or not re.fullmatch(r"[1-9][0-9]*", str(receipt.get("run_attempt", "")))):
        return False, "native qualification receipt is invalid or has different inputs"
    return True, f"identical native inputs qualified by run {receipt['run_id']} on {receipt['commit']}"


def load_receipt(path):
    try:
        value = setup.read_json(path)
        return value if isinstance(value, dict) else None
    except (OSError, ValueError):
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("fingerprint", "decide", "record"))
    parser.add_argument("--fingerprint", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--outputs", type=Path, help="GitHub step output file")
    args = parser.parse_args()
    def emit(values):
        text = "".join(f"{key}={value}\n" for key, value in values.items())
        print(text, end="")
        if args.outputs:
            with args.outputs.open("a") as stream:
                stream.write(text)
    if args.command == "fingerprint":
        current = fingerprint()
        args.fingerprint.write_text(json.dumps(current, indent=2) + "\n")
        emit({"fingerprint": current["sha256"]})
        return
    if args.receipt is None:
        parser.error("--receipt required for decide/record")
    original = setup.read_json(args.fingerprint)
    # Revalidate current source/payloads even on an exact receipt cache hit.
    if original != fingerprint():
        raise ValueError("Native inputs changed during this run")
    if args.command == "decide":
        reuse, reason = reusable(load_receipt(args.receipt), original, os.environ)
        emit({"reuse": str(reuse).lower(), "reason": reason})
        return
    receipt = {"schema": 1, "fingerprint": original["sha256"], "checks": CHECKS,
               "commit": os.environ["GITHUB_SHA"], "run_id": os.environ["GITHUB_RUN_ID"],
               "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"]}
    if not reusable(receipt, original, {})[0]:
        raise ValueError("Invalid native qualification producer identity")
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Recorded completed native qualification: {receipt['run_id']}")


if __name__ == "__main__":
    main()
