#!/usr/bin/env python3
"""Check compiler-pair provenance and independent source snapshot coverage.

This is an artifact/freshness guard. It never substitutes for Lean's kernel
certificate checks, and it does not certify the remaining protocol lowering.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tomllib

import check_setup_artifacts as setup
from export_gkr_translations import FAMILIES, ROOT, LEAN, digest
from gkr_arithmetic_certificate import synthesis


def read(path):
    return json.loads(path.read_text())


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def check_library_ownership(lake):
    """Input dependencies must belong to the library that actually builds a reader.

    Lean 4.31 Lake resolves libraries in reverse declaration order. Roots alone
    do not make a module buildable: their globs must also cover it (or its root).
    """
    def prefix(root, module):
        return module == root or module.startswith(root + ".")

    def matches(glob, module):
        if glob.endswith(".*"):
            return prefix(glob[:-2], module)
        if glob.endswith(".+"):
            return module != glob[:-2] and prefix(glob[:-2], module)
        return glob == module

    def owner(module):
        for library in reversed(lake["lean_lib"]):
            roots = library.get("roots", [library["name"]])
            globs = library.get("globs", roots)
            if (any(matches(glob, module) for glob in globs) or
                    any(prefix(root, module) and any(matches(glob, root) for glob in globs)
                        for root in roots)):
                return library["name"]
        return None

    for module, expected in (
        ("Airbender.Import.GKRCompiler.Import", "GKRCompiler"),
        ("Airbender.Import.GKRCompiler.WiringImport", "GKRCompiler"),
        ("Airbender.Import.Compiler.Arithmetic.AddSubUncached", "GKRCompiler"),
        ("Airbender.Import.Compiler.ArithmeticInstances", "GKRCompiler"),
        ("Airbender.Proofs.GKRCompiler.Native.AddSubUncached", "GKRCompiler"),
        ("Airbender.Import.GKRProtocol.Source", "GKRProtocol"),
        ("Airbender.Import.Compiler.Rows.AddSubUncached", "GKRProtocol"),
        ("Airbender.Proofs.GKRProtocol.Native.AddSubUncached", "GKRProtocol"),
    ):
        if owner(module) != expected:
            raise ValueError(f"Compiler reader/library ownership changed: {module}")


def check(directory=LEAN / "artifacts/compiler", repo=ROOT):
    directory, repo = Path(directory), Path(repo)
    manifest = read(directory / "manifest.json")
    if manifest["format_version"] != 1:
        raise ValueError("Unsupported compiler manifest version")
    pinned = {"Cargo.lock", "cs/examples/export_gkr_translation.rs",
              "formal_verification/lean/scripts/export_gkr_translations.py",
              "formal_verification/lean/scripts/gkr_arithmetic_certificate.py",
              "formal_verification/lean/artifacts/setup/manifest.json"}
    if set(manifest["compiler_inputs"]) != pinned:
        raise ValueError("Compiler producer input inventory changed")
    for relative, expected in manifest["compiler_inputs"].items():
        if digest(repo / relative) != expected:
            raise ValueError(f"Compiler producer input changed: {relative}")
    if subprocess.check_output(["rustc", "--version"], cwd=repo, text=True).strip() != manifest["rustc"]:
        raise ValueError("Compiler Rust toolchain changed")
    setup.check(repo)
    native_manifest = read(repo / "formal_verification/lean/artifacts/setup/manifest.json")
    expected_names = {family + mode for family in FAMILIES for mode in ("-cached", "-uncached")}
    if set(manifest["files"]) != expected_names:
        raise ValueError("Expected all eleven families in both cache modes")
    expected_files = {"manifest.json"} | {
        name + suffix for name in expected_names
        for suffix in (".json", "-certificate.json", "-source.json")}
    if {path.name for path in directory.glob("*.json")} != expected_files:
        raise ValueError("Compiler artifact inventory differs")
    lake = tomllib.loads((repo / "formal_verification/lean/lakefile.toml").read_text())
    check_library_ownership(lake)
    targets = {entry["name"]: entry["path"] for entry in lake["input_file"]}
    compiler = next(entry for entry in lake["lean_lib"] if entry["name"] == "GKRCompiler")
    if "needs" not in compiler or "extraDepTargets" in compiler:
        raise ValueError("Compiler library must use needs to trace actual input-file facets")
    dependencies = {targets[name] for name in compiler["needs"]}
    previous = {}
    for name in sorted(expected_names):
        record = manifest["files"][name]
        paths = [directory / (name + suffix) for suffix in (".json", "-certificate.json", "-source.json")]
        for key, path in zip(("pair_sha256", "certificate_sha256", "source_sha256"), paths):
            if digest(path) != record[key]:
                raise ValueError(f"Compiler artifact changed: {path.name}")
        pair, certificate, source = map(read, paths)
        family, mode = name.rsplit("-", 1)
        if any(pair[key] != value for key, value in
               (("format_version", 1), ("family", family), ("cached", mode == "cached"))):
            raise ValueError(f"Wrong compilation identity: {name}")
        if any(canonical(source[key]) != canonical(pair[key])
               for key in ("format_version", "family", "cached", "source")):
            raise ValueError(f"Source sidecar is detached from compilation: {name}")
        semantic = source["semantic_inputs"]
        counts = pair["source"]["remaining_inputs"]
        for key in ("lookups", "range_checks", "memory_queries", "register_and_indirect_accesses"):
            if len(semantic[key]) != counts[key]:
                raise ValueError(f"Source semantic input count changed: {name}/{key}")
        if ((semantic["executor_machine_state"] is not None) != counts["executor"] or
                (semantic["delegation_circuit_state"] is not None) != counts["delegation"]):
            raise ValueError(f"Source machine-state count changed: {name}")
        if (1 << source["configuration"]["trace_len_log2"] != pair["circuit"]["trace_len"] or
                pair["circuit"]["trace_len"] != record["trace_len"]):
            raise ValueError(f"Compilation geometry changed: {name}")
        independent = {key: source[key] for key in ("source", "semantic_inputs", "configuration")}
        if family in previous and canonical(previous[family]) != canonical(independent):
            raise ValueError(f"Source differs between cache modes: {family}")
        previous[family] = independent
        if synthesis(pair) != certificate or certificate["counts"] != record["counts"]:
            raise ValueError(f"Arithmetic identity synthesis changed: {name}")
        for suffix in (".json", "-certificate.json"):
            if "artifacts/compiler/" + name + suffix not in dependencies:
                raise ValueError(f"Missing Lake compiler input dependency: {name}{suffix}")
        relative = native_manifest["circuit_identities"][family + ".json"]["retained_path"]
        if mode == "cached":
            if not relative.endswith("_layout_no_caches_gkr.json"):
                raise ValueError(f"Unexpected retained circuit path: {relative}")
            relative = relative.replace("_layout_no_caches_gkr.json", "_layout_gkr.json")
        native = read(repo / relative)
        if canonical(pair["circuit"]) != canonical(native):
            raise ValueError(f"Complete compiler output differs from retained native circuit: {name}")
    return len(expected_names)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=LEAN / "artifacts/compiler")
    args = parser.parse_args()
    try:
        print(f"PASS {check(args.directory)} source/compiler pairs, source sidecars and arithmetic certificates; "
              "22 complete retained native identities; kernel checking remains separate")
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        raise SystemExit(f"FAIL {error}") from error
