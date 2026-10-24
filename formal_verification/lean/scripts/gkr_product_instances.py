#!/usr/bin/env python3
"""Generate/check native product instance scaffolding and build it serially.

Run --build inside bounded_fv.py. Actual operands and output groups are read by
the Lean importer; this script does not provide replacement product equations.
"""
import argparse
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, action="append")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ("uncached", "cached"):
            case, name = stem + mode.title(), family + "-" + mode
            module = "GKRProtocol.ProductNative." + case
            path = LEAN / "GKRProtocol/ProductNative" / (case + ".lean")
            content = (
                "import GKRProtocol.NativeProductImport\n"
                f"import GKRProtocol.ConsumerNative.{case}\n\n"
                f"namespace Airbender.Compiler.ProductNative.{case}\n"
                "open Airbender Airbender.Compiler\n"
                "set_option warningAsError true\n"
                "set_option Elab.async false\n"
                "set_option maxRecDepth 32768\n"
                "set_option maxHeartbeats 4000000\n\n"
                f'import_native_products native from "artifacts/compiler/{name}.json"\n\n'
                f"end Airbender.Compiler.ProductNative.{case}\n")
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError(f"native product instance changed: {case}")
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            if args.build:
                print("NATIVE PRODUCT", module, flush=True)
                subprocess.run(["lake", "--no-cache", "build", "+" + module + ":olean"],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS="1"), check=True)


if __name__ == "__main__":
    main()
