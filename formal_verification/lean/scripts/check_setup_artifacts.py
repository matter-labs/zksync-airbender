#!/usr/bin/env python3
"""Check retained native setup provenance without regenerating any artifacts."""

import hashlib
import json
from pathlib import Path
import re

LEAN = Path(__file__).resolve().parents[1]
REPO = LEAN.parent.parent
ARTIFACTS = LEAN / "artifacts/setup"
FAMILIES = {
    "AddSub": "add-sub", "Bigint": "bigint", "Blake2G": "blake-g",
    "Blake2Round": "blake-round", "Keccak": "keccak", "ShiftBinop": "shift-binop",
    "JumpBranchSlt": "jump-branch", "MulDiv": "mul-div", "WordMemory": "word-memory",
    "SubwordMemory": "subword-memory", "UnifiedReduced": "unified",
}


def checked_path(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"Invalid setup provenance path: {relative}")
    return path


def check():
    manifest = json.loads((ARTIFACTS / "manifest.json").read_text())
    if manifest["schema_version"] != 1:
        raise ValueError("Unsupported setup provenance schema")
    expected = set(manifest["artifacts"])
    actual = {path.name for path in ARTIFACTS.glob("*.json")} - {"manifest.json"}
    if actual != expected:
        raise ValueError("Setup artifact inventory differs from manifest")
    for name, metadata in manifest["artifacts"].items():
        path = checked_path(ARTIFACTS, name)
        content = path.read_bytes()
        if hashlib.sha256(content).hexdigest() != metadata["sha256"]:
            raise ValueError(f"Changed setup artifact: {name}")
        data = json.loads(content)
        circuit_hash = hashlib.sha256(json.dumps(
            data["circuit"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if (data["trace_len"] != metadata["trace_len"] or
                len(data["columns"]) != metadata["columns"] or
                circuit_hash != metadata["circuit_sha256"]):
            raise ValueError(f"Changed setup geometry or circuit: {name}")
    for name, digest in manifest["source_sha256"].items():
        if hashlib.sha256(checked_path(REPO, name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"Setup source changed; re-export/review required: {name}")
    for folder, family in FAMILIES.items():
        declaration = LEAN / "Airbender/Review/Circuits" / folder / "Artifact.lean"
        match = re.search(r'import_clean .*? from "([^"]+)"', declaration.read_text())
        if not match:
            raise ValueError(f"Missing retained circuit declaration: {folder}")
        retained = json.loads(checked_path(REPO, str(
            (LEAN / match.group(1)).resolve().relative_to(REPO))).read_text())
        exported = json.loads((ARTIFACTS / f"{family}.json").read_text())
        if exported["circuit"] != retained:
            raise ValueError(f"Setup embeds a different circuit: {family}")
    return len(expected), len(manifest["source_sha256"]), len(FAMILIES)


if __name__ == "__main__":
    try:
        artifacts, sources, circuits = check()
        print(f"PASS {artifacts} setup artifacts, {sources} native source hashes, "
              f"{circuits} retained circuit identities")
    except (OSError, ValueError, KeyError) as error:
        raise SystemExit(f"FAIL {error}") from error
