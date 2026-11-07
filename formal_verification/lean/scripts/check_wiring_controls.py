#!/usr/bin/env python3
"""Require kernel rejection of changed wiring keys and complete graph conditions."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.WiringChecks
open Airbender Airbender.Compiler
namespace WiringControl
'''


def main():
    tests = "Tests.WiringChecks."
    checker = "Airbender.Compiler.WiringChecks.check"
    controls = [(label, f"{checker} {tests}graph {tests}capture = true", f"{checker} {tests}graph {tests}{name} = true")
        for label, name in [("empty producers", "emptyProducers"), ("wrong key", "wrongKey"),
            ("duplicate producer", "duplicateKey"), ("duplicate placement", "duplicatePlacementKey")]]
    controls += [(label, f"{checker} {tests}graph {tests}capture = true", f"{checker} {tests}{name} {tests}capture = true")
        for label, name in [("wrong layer", "wrongLayer"), ("missing output", "missingOutput"),
            ("stale producer table", "staleProducerTable")]]
    controls += [("cache dependency", f"{checker} {tests}cachedGraph {tests}cachedCapture = true",
                  f"{checker} {tests}badCache {tests}cachedCapture = true")]
    controls += [
        ("complete producer binding",
         f"{tests}capture.producers.toList = WiringChecks.KeySort.sort ({tests}graph.produced.map AddressUniqueChecks.addressCode)",
         f"{tests}wrongKey.producers.toList = WiringChecks.KeySort.sort ({tests}graph.produced.map AddressUniqueChecks.addressCode)"),
        ("complete placement binding",
         f"{tests}capture.placements.toList = WiringChecks.KeySort.sort ({tests}graph.placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))",
         f"{tests}duplicatePlacementKey.placements.toList = WiringChecks.KeySort.sort ({tests}graph.placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))"),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding result : {statement}\nend WiringControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-wiring-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} failed:\n" + result.stdout[-2000:])
            if mutated and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
                raise SystemExit(f"Changed {label} did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS ten exact bindings and results; kernel rejects all ten mutations")


if __name__ == "__main__":
    main()
