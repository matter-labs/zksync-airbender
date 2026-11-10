#!/usr/bin/env python3
"""Require kernel rejection of changed placement data and lookup witnesses."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.CleanPlacementChecks
open Airbender Airbender.Compiler
namespace CleanPlacementControl
'''


def main():
    checker = "Airbender.Compiler.CleanPlacementChecks.check"
    tests = "Tests.CleanPlacementChecks."
    controls = [(label, f"{checker} {tests}capture = true", f"{checker} {tests}{name} = true")
                for label, name in [("index", "wrongIndex"), ("code", "wrongCode"),
                                    ("outside index", "outside"), ("forged size", "forgedSize")]]
    controls += [
        ("bank binding",
         f"{tests}capture.bank.toList = {tests}entries.map AddressUniqueChecks.addressCode",
         f"{tests}capture.bank.toList = ([GKRAddress.BaseLayerWitness 1, .BaseLayerMemory 1, .Cached 2 3]).map AddressUniqueChecks.addressCode"),
        ("complete placement binding",
         f"{tests}capture.references.map Prod.fst = {tests}placements.map AddressUniqueChecks.addressCode",
         f"{tests}capture.references.map Prod.fst = ([GKRAddress.Cached 2 3]).map AddressUniqueChecks.addressCode"),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding result : {statement}\nend CleanPlacementControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-clean-placement-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} failed:\n" + result.stdout[-2000:])
            if mutated and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
                raise SystemExit(f"Changed {label} did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS six exact bindings and results; kernel rejects all six mutations")


if __name__ == "__main__":
    main()
