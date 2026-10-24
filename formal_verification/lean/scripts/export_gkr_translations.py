#!/usr/bin/env python3
"""Capture actual source/compiler pairs and synthesize arithmetic identities.

Run inside bounded_fv.py: all compiler invocations are sequential, caches do
not replace native circuit construction, and unsupported identities fail.
Lean kernel checking is a separate required step after this producer.
"""
import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

from gkr_arithmetic_certificate import synthesis

ROOT = Path(__file__).resolve().parents[3]
LEAN = Path(__file__).resolve().parents[1]
FAMILIES = ["add-sub", "jump-branch", "mul-div", "shift-binop", "word-memory",
            "subword-memory", "unified", "bigint", "blake-g", "blake-round", "keccak"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json_if_changed(path, value, *, indent=None, sort_keys=False):
    encoded = (json.dumps(value, indent=indent, sort_keys=sort_keys,
                          separators=None if indent else (",", ":")) + "\n").encode()
    if not path.exists() or path.read_bytes() != encoded:
        path.write_bytes(encoded)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=LEAN / "artifacts/compiler")
    parser.add_argument("--family", choices=FAMILIES, action="append")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ)
    environment.pop("CI", None)
    environment["CARGO_PROFILE_DEV_DEBUG"] = "0"
    environment["CARGO_BUILD_JOBS"] = "1"
    records, errors = {}, []
    for family in args.family or FAMILIES:
        original_source = None
        for cached in (False, True):
            name = family + ("-cached" if cached else "-uncached")
            pair_path = output / (name + ".json")
            command = ["cargo", "run", "--locked", "-p", "cs", "--example",
                       "export_gkr_translation", "--", family, str(pair_path)]
            if cached:
                command.append("--cached")
            subprocess.run(command, cwd=ROOT, env=environment, check=True)
            pair = json.loads(pair_path.read_text())
            source_path = output / (name + "-source.json")
            complete_source = json.loads(source_path.read_text())
            if pair["family"] != family or pair["cached"] != cached:
                raise ValueError("native exporter returned a different compilation")
            if any(complete_source[key] != pair[key]
                   for key in ("format_version", "family", "cached", "source")):
                raise ValueError("source sidecar does not belong to the compilation")
            if 1 << complete_source["configuration"]["trace_len_log2"] != pair["circuit"]["trace_len"]:
                raise ValueError("source sidecar has a different trace length")
            if original_source is None:
                original_source = pair["source"]
            elif pair["source"] != original_source:
                raise ValueError(f"cached and uncached source snapshots disagree: {family}")
            record = {"pair_sha256": digest(pair_path), "cached": cached,
                      "source_sha256": digest(source_path),
                      "trace_len": pair["circuit"]["trace_len"]}
            try:
                certificate = synthesis(pair)
                certificate_path = output / (name + "-certificate.json")
                write_json_if_changed(certificate_path, certificate)
                record.update(certificate_sha256=digest(certificate_path), counts=certificate["counts"])
                print(name, json.dumps(certificate["counts"], sort_keys=True), flush=True)
            except ValueError as error:
                record["synthesis_error"] = str(error)
                errors.append(name + ": " + str(error))
                print("UNSUPPORTED", errors[-1], flush=True)
            records[name] = record
    pinned = [ROOT / "Cargo.lock", ROOT / "cs/examples/export_gkr_translation.rs",
              Path(__file__).resolve(), Path(__file__).with_name("gkr_arithmetic_certificate.py"),
              LEAN / "artifacts/setup/manifest.json"]
    manifest = {"format_version": 1,
                "scope": "source arithmetic slice; lookup/memory/cache protocol lowering is not certified",
                "compiler_inputs": {str(path.relative_to(ROOT)): digest(path) for path in pinned},
                "rustc": subprocess.check_output(["rustc", "--version"], cwd=ROOT, text=True).strip(),
                "files": records}
    write_json_if_changed(output / "manifest.json", manifest, indent=2, sort_keys=True)
    if errors:
        raise SystemExit("Certificate synthesis incomplete:\n" + "\n".join(errors))
    print(f"Captured {len(records)} compilations; Lean kernel checks remain required.", flush=True)


if __name__ == "__main__":
    main()
