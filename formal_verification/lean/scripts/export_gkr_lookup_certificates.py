#!/usr/bin/env python3
"""Synthesize lookup-field certificates for retained native compiler captures.

This does not rerun Rust or establish kernel checking. Parent capture provenance
must pass first; it is bound without repinning or replacing native source/output.
"""
import json

from check_gkr_translations import check
from export_gkr_translations import FAMILIES, LEAN, ROOT, digest, write_json_if_changed
from gkr_lookup_certificate import synthesis


def main():
    check()
    parent = LEAN / "artifacts/compiler"
    output = parent / "lookup"
    output.mkdir(exist_ok=True)
    records = {}
    for family in FAMILIES:
        for mode in ("cached", "uncached"):
            name = family + "-" + mode
            pair, source = parent / (name + ".json"), parent / (name + "-source.json")
            certificate = synthesis(json.loads(pair.read_text()), json.loads(source.read_text()))
            path = output / (name + ".json")
            write_json_if_changed(path, certificate)
            records[name] = {"sha256": digest(path), "pair_sha256": digest(pair),
                             "source_sha256": digest(source), "counts": certificate["counts"]}
            print(name, certificate["counts"]["agreements"], "synthesized field identities")
    inputs = [ROOT / "formal_verification/lean/scripts/export_gkr_lookup_certificates.py",
              ROOT / "formal_verification/lean/scripts/gkr_lookup_certificate.py",
              ROOT / "cs/src/definitions/table_type.rs"]
    manifest = {"format_version": 1,
                "scope": "source lookup/range16/decoder fields only; graph reduction, cache binding and RAM remain required",
                "parent_manifest_sha256": digest(parent / "manifest.json"),
                "synthesizer_inputs": {str(path.relative_to(ROOT)): digest(path) for path in inputs},
                "files": records}
    write_json_if_changed(output / "manifest.json", manifest, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
