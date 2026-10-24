#!/usr/bin/env python3
"""Guard lookup-field certificate provenance; kernel replay remains separate."""
import json
import tomllib

from check_gkr_translations import check
from export_gkr_translations import FAMILIES, LEAN, ROOT, digest
from gkr_lookup_certificate import synthesis


def verify():
    check()
    parent = LEAN / "artifacts/compiler"
    output = parent / "lookup"
    manifest = json.loads((output / "manifest.json").read_text())
    if manifest["format_version"] != 1 or manifest["parent_manifest_sha256"] != digest(parent / "manifest.json"):
        raise ValueError("Lookup certificate parent provenance changed")
    inputs = {"formal_verification/lean/scripts/export_gkr_lookup_certificates.py",
              "formal_verification/lean/scripts/gkr_lookup_certificate.py", "cs/src/definitions/table_type.rs"}
    if set(manifest["synthesizer_inputs"]) != inputs:
        raise ValueError("Lookup synthesizer inventory changed")
    for relative, expected in manifest["synthesizer_inputs"].items():
        if digest(ROOT / relative) != expected:
            raise ValueError(f"Lookup synthesizer input changed: {relative}")
    names = {family + "-" + mode for family in FAMILIES for mode in ("cached", "uncached")}
    if set(manifest["files"]) != names or {path.name for path in output.glob("*.json")} != {"manifest.json"} | {name + ".json" for name in names}:
        raise ValueError("Lookup certificate compilation inventory changed")
    lake = tomllib.loads((LEAN / "lakefile.toml").read_text())
    targets = {entry["name"]: entry["path"] for entry in lake["input_file"]}
    library = next(entry for entry in lake["lean_lib"] if entry["name"] == "GKRProtocol")
    if "needs" not in library or "extraDepTargets" in library:
        raise ValueError("Lookup library must use needs to trace actual input-file facets")
    dependencies = {targets[name] for name in library["needs"]}
    for name in sorted(names):
        pair, source, path = parent / (name + ".json"), parent / (name + "-source.json"), output / (name + ".json")
        record = manifest["files"][name]
        if any(digest(file) != record[key] for file, key in
               ((pair, "pair_sha256"), (source, "source_sha256"), (path, "sha256"))):
            raise ValueError(f"Lookup compilation input or certificate changed: {name}")
        certificate = json.loads(path.read_text())
        if synthesis(json.loads(pair.read_text()), json.loads(source.read_text())) != certificate or record["counts"] != certificate["counts"]:
            raise ValueError(f"Lookup identity synthesis changed: {name}")
        if any(relative not in dependencies for relative in
               ("artifacts/compiler/" + name + ".json", "artifacts/compiler/" + name + "-source.json",
                "artifacts/compiler/lookup/" + name + ".json")):
            raise ValueError(f"Missing Lake lookup input dependency: {name}")
    return len(names)


if __name__ == "__main__":
    print(f"PASS {verify()} lookup-field certificate provenance guards; kernel replay remains separate")
