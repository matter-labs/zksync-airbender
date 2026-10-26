#!/usr/bin/env python3
"""Generate/check wiring module shards, or build them with one compiler at a time.

The generated modules read the actual native pair. This script supplies only
module boundaries and check ranges; no replacement ports or proof facts.
Run --build under bounded_fv.py. It uses ordinary Lake dependency checks.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

from export_gkr_translations import FAMILIES, LEAN

CASES = ["AddSub", "JumpBranch", "MulDiv", "ShiftBinop", "WordMemory", "SubwordMemory",
         "Unified", "Bigint", "BlakeG", "BlakeRound", "Keccak"]


def module(case, path, imports, phase, first=0, count=0, public=False):
    namespace = "Airbender.Compiler.WiringNative." + case
    return "".join("import " + name + "\n" for name in imports) + f"""
namespace {namespace}
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_wiring native from "{path}" phase "{phase}" start {first} count {count}
""" + ("\ntheorem wiring_valid : native.graph.Valid := native.sound\n" if public else "") + "\nend " + namespace + "\n"


def generated():
    files, jobs = {}, []
    for family, stem in zip(FAMILIES, CASES):
        for mode, suffix in (("uncached", "Uncached"), ("cached", "Cached")):
            case = stem + suffix
            path = f"artifacts/compiler/{family}-{mode}.json"
            pair = json.loads((LEAN / path).read_text())
            gates = [gate["enforced_relation"] for layer in pair["circuit"]["layers"]
                     for gate in layer["gates"] + layer["gates_with_external_connections"]]
            nc = sum(len(layer["cached_relations"]) for layer in pair["circuit"]["layers"])
            outputs = [body.get("output") for gate in gates for body in gate.values() if "output" in body]
            np = nc + sum(len(output) if isinstance(output, list) else 1 for output in outputs)
            data = "Airbender.Proofs.GKRCompiler.WiringData." + case
            files[data] = module(case, path, ["Airbender.Import.GKRCompiler.WiringImport"], "data")
            jobs.append(data)
            geometry = "Airbender.Proofs.GKRCompiler.WiringParts." + case + "Geometry"
            files[geometry] = module(case, path, [data], "geometry")
            jobs.append(geometry)
            imports = [geometry]
            for phase, count in (("unique", np), ("placement", pair["source"]["num_variables"]),
                                 ("gates", len(gates)), ("caches", nc)):
                for first in range(0, count, 64):
                    name = "Airbender.Proofs.GKRCompiler.WiringParts." + case + phase.title() + str(first // 64)
                    files[name] = module(case, path, [data], phase, first, min(64, count - first))
                    jobs.append(name)
                    imports.append(name)
            name = "Airbender.Proofs.GKRCompiler.WiringNative." + case
            files[name] = module(case, path, imports, "assemble", public=True)
            jobs.append(name)
    return files, jobs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write changed generated module scaffolding")
    parser.add_argument("--build", action="store_true", help="Check scaffolding, then build each shard sequentially")
    parser.add_argument("--family", choices=FAMILIES, action="append", help="Limit builds, not inventory checking")
    args = parser.parse_args()
    files, jobs = generated()
    for name, content in files.items():
        path = LEAN / (name.replace(".", "/") + ".lean")
        if not path.exists() or path.read_text() != content:
            if not args.write:
                raise SystemExit(f"Stale wiring scaffolding: {name}; regenerate with --write")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    actual = {str(path.relative_to(LEAN).with_suffix("")).replace("/", ".")
              for folder in ("WiringData", "WiringParts", "WiringNative")
              for path in (LEAN / "Airbender/Proofs/GKRCompiler" / folder).glob("*.lean")}
    if actual != set(files):
        raise SystemExit("Unexpected wiring scaffolding files; review before removing stale shards")
    if args.build:
        stems = [CASES[FAMILIES.index(family)] for family in args.family or FAMILIES]
        environment = dict(os.environ, LEAN_NUM_THREADS="1")
        for name in jobs:
            case = name.rsplit(".", 1)[1]
            if not any(case.startswith(stem) for stem in stems):
                continue
            print("WIRING", name, flush=True)
            subprocess.run(["lake", "--no-cache", "build", "+" + name + ":olean"],
                           cwd=LEAN, env=environment, check=True)
    print(f"PASS wiring scaffolding for 22 compilations; {len(jobs)} serial module targets", flush=True)


if __name__ == "__main__":
    main()
