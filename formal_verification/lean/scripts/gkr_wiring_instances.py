#!/usr/bin/env python3
"""Generate complete wiring captures, or build them with one compiler at a time.

The generated modules read the actual native pair. This script supplies only
data scaffolds and complete certificates; no replacement ports or proof facts.
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

import_compiler_wiring native from "{path}" phase "{phase}" start {first} count {count}
""" + ("\ntheorem wiring_valid : native.graph.Valid := native.sound\n" if public else "") + "\nend " + namespace + "\n"


def generated():
    from gkr_packed_wiring import load, modules, native_module
    files, jobs = {}, []
    for family, stem in zip(FAMILIES, CASES, strict=True):
        for mode, suffix in (("uncached", "Uncached"), ("cached", "Cached")):
            case = stem + suffix
            name = family + '-' + mode
            path = f"artifacts/compiler/{name}.json"
            payload = load(name)
            data = "Airbender.Proofs.GKRCompiler.WiringData." + case
            files[data] = module(case, path, ["Airbender.Import.GKRCompiler.WiringImport"], "data")
            jobs.append(data)
            for relative, content in modules(case, payload).items():
                owner = relative.removesuffix('.lean').replace('/', '.')
                files[owner] = content
                jobs.append(owner)
            native = "Airbender.Proofs.GKRCompiler.WiringNative." + case
            files[native] = native_module(case, name, payload)
            jobs.append(native)
    # Keep the two established import paths after source slots disappear.
    for suffix in ("Cached", "Uncached"):
        case = "Unified" + suffix
        retired = "Airbender.Proofs.GKRCompiler.WiringParts." + case + "Placement2"
        files[retired] = "import Airbender.Proofs.GKRCompiler.WiringNative." + case + "\n"
        jobs.append(retired)
    return files, jobs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write changed generated module scaffolding")
    parser.add_argument("--build", action="store_true", help="Check scaffolding, then build each capture module sequentially")
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
              for folder in ("WiringData", "WiringParts", "WiringNative", "WiringCheckNative")
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
