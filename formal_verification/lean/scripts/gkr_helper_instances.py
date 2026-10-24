#!/usr/bin/env python3
"""Select actual timestamp consumers; Lean reconstructs source helper queries.

Only addresses, occurrence/definition selectors and copy witnesses are emitted.
No replacement source or native equation is certificate data.
"""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_lookup_source_certificate import synthesis as lookup_synthesis
from gkr_memory_certificate import synthesis as memory_synthesis


def synthesis(pair, snapshot, lookup_certificate):
    lookup = lookup_synthesis(pair, lookup_certificate)
    memory = memory_synthesis(pair, snapshot)
    operands = []
    setup = None
    for operand in lookup["operands"]:
        if operand["group"] != "LookupTimestamps":
            continue
        if operand["kind"] == "setup":
            if setup is not None:
                raise ValueError("duplicate timestamp setup leaf")
            setup = operand["native_leaf"]
            continue
        if operand["kind"] != "timestamp":
            raise ValueError("unexpected timestamp operand kind")
        operands.append({name: operand[name] for name in ("native_leaf", "locator", "expansion", "source_index")}
                        | {"witness": []})
    if setup is None:
        raise ValueError("missing timestamp setup leaf")
    return {"format_version": 1, "addresses": memory["addresses"], "operands": operands,
            "setup_leaf": setup, "group": lookup["groups"]["LookupTimestamps"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, action="append")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    root = LEAN / "artifacts/compiler"
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ("uncached", "cached"):
            name, case = family + "-" + mode, stem + mode.title()
            result = synthesis(json.loads((root / (name + ".json")).read_text()),
                               json.loads((root / (name + "-source.json")).read_text()),
                               json.loads((root / "lookup" / (name + ".json")).read_text()))
            module = "GKRProtocol.HelperNative." + case
            selectors = json.dumps(json.dumps(result, separators=(",", ":")))
            content = ("import GKRProtocol.HelperImport\n"
                       f"import GKRProtocol.MemoryNative.{case}\n"
                       f"import GKRProtocol.LookupNative.{case}\n\n"
                       f"namespace Airbender.Compiler.HelperNative.{case}\n"
                       "open Airbender Airbender.Compiler\n"
                       "set_option warningAsError true\n"
                       "set_option Elab.async false\n"
                       "set_option maxRecDepth 32768\n"
                       "set_option maxHeartbeats 4000000\n\n"
                       f'import_source_helpers native from "artifacts/compiler/{name}.json"\n'
                       f'  source "artifacts/compiler/{name}-source.json"\n'
                       f"  selectors {selectors}\n"
                       f"  memory_model Airbender.Compiler.MemoryNative.{case}.native\n"
                       f"  lookup_model Airbender.Compiler.LookupNative.{case}.native\n"
                       f"  typing Airbender.Compiler.ConsumerNative.{case}.native.typing\n\n"
                       f"end Airbender.Compiler.HelperNative.{case}\n")
            destination = LEAN / "GKRProtocol/HelperNative" / (case + ".lean")
            if args.check and (not destination.exists() or destination.read_text() != content):
                raise ValueError(f"source helper selectors changed: {case}")
            if args.write and (not destination.exists() or destination.read_text() != content):
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(content)
            print(name, len(result["operands"]), "timestamp helper queries", flush=True)
            if args.build:
                subprocess.run(["lake", "--no-cache", "build", "+" + module + ":olean"],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS="1"), check=True)


if __name__ == "__main__":
    main()
