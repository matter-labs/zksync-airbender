#!/usr/bin/env python3
"""Validate retained setup bytes, native sources and explicit circuit identities.

This is a drift guard, not Rust refinement. Native reconstruction is performed
separately by check_setup_freshness.py. Python 3.11+ is required for tomllib.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import tomllib

LEAN = Path(__file__).resolve().parents[1]
REPO = LEAN.parent.parent
ARTIFACTS = LEAN / "artifacts/setup"
SOURCE_ROOT_CRATES = ("cs", "execution_prover", "prover")
MANIFEST_FILES = {"manifest.json", "native-evidence.json"}
PRODUCTION_CIRCUITS = {
    "add-sub": "add_sub_lui_auipc_mop", "bigint": "bigint_with_extended_control",
    "blake-g": "blake2_g_function", "blake-round": "blake2_with_extended_control",
    "keccak": "keccak_special5", "shift-binop": "shift_binop",
    "jump-branch": "jump_branch_slt", "mul-div": "unsigned_mul_div",
    "word-memory": "mem_word_only", "subword-memory": "mem_subword_only",
    "unified": "unified_reduced_machine", "inits-and-teardowns": "inits_and_teardowns",
}
NATIVE_LOCK = "formal_verification/lean/artifacts/setup/native-cargo.lock"
SMOKE_TEST = "gkr::prover::setup::tests::setup_json_roundtrip_preserves_materialized_columns_and_program"


def checked_path(root, relative):
    root = Path(root).resolve()
    path = (root / relative).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise ValueError(f"Invalid setup provenance path: {relative}")
    return path


def sha256(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def circuit_digest(circuit):
    return hashlib.sha256(json.dumps(circuit, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def read_json(path):
    # Reject duplicate keys rather than silently accepting a different payload.
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"Duplicate JSON key {key!r}: {path}")
            result[key] = value
        return result
    def invalid_constant(value):
        raise ValueError(f"Nonfinite JSON number {value}: {path}")
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_constant=invalid_constant)


def source_inventory(repo):
    """Conservative local Cargo closure, including optional/target/dev branches.

    Pin every nonempty source/include file in these crates, not just files guessed
    to affect one layout. It deliberately overapproximates active feature use.
    Empty files are excluded from the coverage count. Cargo.lock pins external
    dependency selection; this inventory makes no external-source review claim.
    """
    repo = Path(repo).resolve()
    workspace = tomllib.loads(checked_path(repo, "Cargo.toml").read_text())["workspace"]
    dependencies = workspace["dependencies"]
    pending = [repo / name for name in SOURCE_ROOT_CRATES]
    crates, paths = set(), {"Cargo.toml", "rust-toolchain.toml"}
    while pending:
        crate = pending.pop().resolve()
        if not crate.is_relative_to(repo) or (crate / "Cargo.toml").is_symlink():
            raise ValueError(f"Nonlocal source crate: {crate}")
        relative = crate.relative_to(repo).as_posix()
        if relative in crates:
            continue
        crates.add(relative)
        manifest = checked_path(repo, relative + "/Cargo.toml")
        data = tomllib.loads(manifest.read_text())
        paths.add(manifest.relative_to(repo).as_posix())
        tables = [data.get(key, {}) for key in ("dependencies", "dev-dependencies", "build-dependencies")]
        for target in data.get("target", {}).values():
            tables.extend(target.get(key, {}) for key in ("dependencies", "dev-dependencies", "build-dependencies"))
        for table in tables:
            for name, value in table.items():
                base = crate
                if isinstance(value, dict) and value.get("workspace"):
                    value, base = dependencies[name], repo
                if isinstance(value, dict) and "path" in value:
                    pending.append(base / value["path"])
        for directory in (crate / "src", crate / "generated"):
            if directory.is_dir():
                for path in directory.rglob("*"):
                    if path.is_file() and path.stat().st_size:
                        paths.add(path.relative_to(repo).as_posix())
        for path in (crate / "build.rs",):
            if path.is_file() and path.stat().st_size:
                paths.add(path.relative_to(repo).as_posix())
    paths.add("execution_prover/examples/export_setup_json.rs")
    for path in (repo / ".cargo").glob("config*"):
        if path.is_file():
            paths.add(path.relative_to(repo).as_posix())
    # Capture literal includes even when they live outside src/generated. Dynamic
    # includes need the native dep-info cross-check; never guess OUT_DIR contents.
    pending_files = list(paths)
    seen = set()
    while pending_files:
        relative = pending_files.pop()
        if relative in seen:
            continue
        seen.add(relative)
        path = checked_path(repo, relative)
        if path.suffix != ".rs":
            continue
        for include in re.findall(r'\binclude(?:_bytes|_str)?!\s*\(\s*"([^"\n]+)"', path.read_text()):
            included = checked_path(repo, (path.parent / include).relative_to(repo).as_posix())
            name = included.relative_to(repo).as_posix()
            if included.stat().st_size and name not in paths:
                paths.add(name)
                pending_files.append(name)
    return sorted(paths), sorted(crates)


def prepare_native_lock(repo, manifest, prepare=False):
    """Preserve dependency selection; create an absent ignored lock exclusively.

    A differing existing lock is never overwritten, even with prepare=True.
    """
    repo = Path(repo).resolve()
    if manifest["cargo_lock_source"] != NATIVE_LOCK:
        raise ValueError("Wrong retained native Cargo lock provenance path")
    pinned = checked_path(repo, NATIVE_LOCK)
    if sha256(pinned) != manifest["cargo_lock_sha256"]:
        raise ValueError("Retained native Cargo lock changed; dependency-selection review required")
    destination = repo / "Cargo.lock"
    created = False
    if not destination.exists():
        if not prepare:
            raise ValueError("Native Cargo.lock absent; run check_setup_artifacts.py --prepare-lock")
        try:
            with destination.open("xb") as stream:
                stream.write(pinned.read_bytes())
            created = True
        except FileExistsError:
            # Concurrent creation does not permit replacing its dependency choice.
            pass
    if sha256(checked_path(repo, "Cargo.lock")) != manifest["cargo_lock_sha256"]:
        raise ValueError("Existing native Cargo.lock differs; refusing to overwrite dependency selection")
    return created


def check_sources(repo, manifest):
    expected, crates = source_inventory(repo)
    prepare_native_lock(repo, manifest)
    inventory = manifest["source_inventory"]
    if inventory["root_crates"] != list(SOURCE_ROOT_CRATES) or inventory["local_crates"] != crates:
        raise ValueError("Setup native Cargo closure changed; review source inventory")
    if set(expected) != set(manifest["source_sha256"]):
        missing = sorted(set(expected) - set(manifest["source_sha256"]))
        extra = sorted(set(manifest["source_sha256"]) - set(expected))
        raise ValueError(f"Setup source inventory changed; missing={missing[:8]}, obsolete={extra[:8]}")
    for name in expected:
        if sha256(checked_path(repo, name)) != manifest["source_sha256"][name]:
            raise ValueError(f"Setup source changed; re-export/review required: {name}")


def check_artifact(path, metadata):
    if sha256(path) != metadata["sha256"]:
        raise ValueError(f"Changed setup artifact: {Path(path).name}")
    data = read_json(path)
    if (data["trace_len"] != metadata["trace_len"] or
            len(data["columns"]) != metadata["columns"] or
            circuit_digest(data["circuit"]) != metadata["circuit_sha256"]):
        raise ValueError(f"Changed setup geometry or circuit: {Path(path).name}")
    return data


def check_identities(repo, artifacts, manifest):
    identities = manifest["circuit_identities"]
    expected = {name + ".json" for name in PRODUCTION_CIRCUITS} | {"decoder-smoke.json"}
    if set(identities) != expected:
        raise ValueError("Expected twelve production identities and one derived smoke identity")
    for family, basename in PRODUCTION_CIRCUITS.items():
        name = family + ".json"
        identity = identities[name]
        relative = f"cs/compiled_circuits/{basename}_layout_no_caches_gkr.json"
        if identity != {"kind": "production", "retained_path": relative}:
            raise ValueError(f"Wrong production circuit identity metadata: {name}")
        if circuit_digest(read_json(artifacts / name)["circuit"]) != circuit_digest(read_json(checked_path(repo, relative))):
            raise ValueError(f"Setup embeds a different retained circuit: {family}")
    check_smoke_identity(repo, artifacts, identities["decoder-smoke.json"])


def check_smoke_identity(repo, artifacts, smoke):
    base = "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"
    if (smoke.get("kind") != "native-derived-fixture" or smoke.get("base_path") != base or
            smoke.get("constructor_path") != "prover/src/gkr/prover/setup_tests.rs" or
            smoke.get("constructor_test") != SMOKE_TEST):
        raise ValueError("Wrong derived smoke circuit identity metadata")
    if sha256(checked_path(repo, base)) != smoke["base_sha256"]:
        raise ValueError("Smoke retained ADD/SUB base changed; reconstruct derived fixture")
    if sha256(checked_path(repo, smoke["constructor_path"])) != smoke["constructor_sha256"]:
        raise ValueError("Smoke native derivation changed; reconstruct derived fixture")
    if circuit_digest(read_json(artifacts / "decoder-smoke.json")["circuit"]) != smoke["derived_circuit_sha256"]:
        raise ValueError("Changed derived smoke circuit identity")


def check_dep_info(repo, manifest, paths, required_inputs=()):
    """Cross-check real native dep-info against pinned local inputs.

    Caller supplies dep-info from its scoped native build, including dependency
    crates. Unrelated cached dep-info is not a substitute for those jobs.
    """
    repo = Path(repo).resolve()
    allowed = set(manifest["source_sha256"])
    allowed.update(item["retained_path"] for item in manifest["circuit_identities"].values() if item["kind"] == "production")
    observed = set()
    for path in paths:
        source = Path(path).read_text().replace("\\\n", " ")
        for line in source.splitlines():
            if ": " not in line:
                continue
            for token in shlex.split(line.split(": ", 1)[1]):
                candidate = Path(token)
                if not candidate.is_absolute():
                    candidate = repo / candidate
                candidate = candidate.resolve()
                if candidate.is_relative_to(repo) and candidate.is_file():
                    name = candidate.relative_to(repo).as_posix()
                    if name.startswith("target/"):
                        # OUT_DIR outputs are reconstructed by Cargo; their source
                        # build scripts are pinned. They are not reviewed sources.
                        continue
                    observed.add(name)
    if not observed:
        raise ValueError("No repository inputs found in native dep-info")
    absent = sorted(set(required_inputs) - observed)
    if absent:
        raise ValueError(f"Native dep-info is incomplete for selected commands: {absent}")
    missing = sorted(observed - allowed)
    if missing:
        raise ValueError(f"Native dep-info has unpinned source/include inputs: {missing[:12]}")
    return len(observed)


def check(repo=REPO, artifacts=None, dep_info=()):
    repo = Path(repo).resolve()
    artifacts = Path(artifacts) if artifacts else repo / "formal_verification/lean/artifacts/setup"
    manifest = read_json(artifacts / "manifest.json")
    if manifest["schema_version"] != 2:
        raise ValueError("Unsupported setup provenance manifest schema")
    expected = {family + ".json" for family in PRODUCTION_CIRCUITS} | {"decoder-smoke.json"}
    actual = {path.name for path in artifacts.glob("*.json")} - MANIFEST_FILES
    if actual != expected or set(manifest["artifacts"]) != expected:
        raise ValueError("Setup artifact inventory differs from required thirteen artifacts")
    for name, metadata in manifest["artifacts"].items():
        check_artifact(checked_path(artifacts, name), metadata)
    check_sources(repo, manifest)
    check_identities(repo, artifacts, manifest)
    if dep_info:
        check_dep_info(repo, manifest, dep_info)
    return len(expected), len(manifest["source_sha256"]), len(PRODUCTION_CIRCUITS)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--dep-info", type=Path, action="append", default=[])
    parser.add_argument("--prepare-lock", action="store_true", help="Copy retained native lock only when absent; verify, never overwrite, an existing root lock")
    args = parser.parse_args()
    try:
        if args.prepare_lock:
            directory = args.artifacts or args.repo / "formal_verification/lean/artifacts/setup"
            created = prepare_native_lock(args.repo, read_json(directory / "manifest.json"), prepare=True)
            print("Prepared ignored Cargo.lock from retained dependency selection" if created else "Verified existing ignored Cargo.lock; unchanged")
        artifacts, sources, circuits = check(args.repo, args.artifacts, args.dep_info)
        print(f"PASS {artifacts} setup artifacts, {sources} native source hashes, "
              f"{circuits} production circuit identities, 1 native derived-fixture identity")
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"FAIL {error}") from error
