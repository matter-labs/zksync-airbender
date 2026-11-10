#!/usr/bin/env python3
"""Guard eight deliberately re-inspected native evidence files against drift.

    The manifest records source observations and historical inspections separately.
    Hash agreement does not establish Rust refinement or cryptographic soundness.
"""

import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
SOURCES = {
    "full_statement_verifier/src/unrolled_proof_statement.rs",
    "full_statement_verifier/src/unified_circuit_statement.rs",
    "prover/src/definitions/mod.rs", "cs/src/definitions/constants.rs",
    "cs/src/gkr_compiler/memory_like_grand_product.rs",
    "cs/src/gkr_compiler/family_circuit.rs",
    "prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/mask_into_identity.rs",
    "verifier/src/generated/add_sub_lui_auipc_mop/sec_100/gkr.rs",
}


def check(repo=REPO, manifest_path=None):
    repo = Path(repo).resolve()
    manifest_path = manifest_path or repo / "formal_verification/lean/artifacts/setup/native-evidence.json"
    manifest = json.loads(Path(manifest_path).read_text())
    if manifest["schema_version"] != 1 or set(manifest["sources"]) != SOURCES:
        raise ValueError("Native evidence inventory must contain the exact eight reviewed paths")
    for relative, record in manifest["sources"].items():
        path = (repo / relative).resolve()
        if not path.is_relative_to(repo) or not path.is_file():
            raise ValueError(f"Missing native evidence source: {relative}")
        data = path.read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if hashlib.sha256(data).hexdigest() != record["sha256"] or blob != record["git_blob"]:
            raise ValueError(f"Native evidence changed; inspect behavior before updating pins: {relative}")
        if not record["observation"] or not record["inspected_spans"] or not record["historical_inspections"]:
            raise ValueError(f"Missing current/historical inspection context: {relative}")
    historical = manifest["retrieved_historical_source"]
    if (historical["revision"] != "1f4a8455e9f893a1ffb3d23ad79918f243b28aca" or
            historical["path"] != "full_statement_verifier/src/unrolled_proof_statement.rs" or
            not historical["git_blob"]):
        raise ValueError("Missing corrected historical-source retrieval record")
    return len(SOURCES)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    try:
        count = check(args.repo, args.manifest)
        print(f"PASS {count} current native evidence pins; historical inspections retained separately")
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"FAIL {error}") from error
