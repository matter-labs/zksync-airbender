#!/usr/bin/env python3
"""Require exact packed checks and kernel rejection of changed certificates."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedNormalizationTrace
import Tests.NumericArithmeticTrace
open Airbender.Compiler.NumericPolynomialChecks
open PackedNormalization
open Tests.PackedNormalizationTrace
namespace PackedNormalizationControl
'''


def main():
    controls = [
        ("position", "check 7 [wrongPosition]"),
        ("input", "check 7 [wrongInput]"),
        ("expected", "check 7 [wrongExpected]"),
        ("missing step", "check 7 [missingStep]"),
        ("extra step", "check 7 [extraStep]"),
        ("length", "check 7 [wrongLength]"),
        ("coefficient bound", "boundsCheck [(coefficientBase, 0)]"),
        ("key bound", "boundsCheck [(1, coefficientBase)]"),
        ("zero modulus", "check 0 [row]"),
        ("large modulus", "check (coefficientBase + 1) [row]"),
    ]
    controls = [(label, "check 7 [row]", changed) for label, changed in controls]
    controls.append(("imported input binding",
                     "Airbender.Compiler.NumericArithmeticTrace.bindingCheck [(expected, input)] Tests.NumericArithmeticTrace.importedRows",
                     "Airbender.Compiler.NumericArithmeticTrace.bindingCheck [(expected, [(2, [1, 0]), (5, [0, 1]), (6, []), (1, [2])])] Tests.NumericArithmeticTrace.importedRows"))
    for label, exact, changed in controls:
        for mutated, expression in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding result : {expression} = true\nend PackedNormalizationControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-packed-normalization-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} control failed:\n" + result.stdout[-2000:])
            if mutated and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
                raise SystemExit(f"Changed {label} did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS eleven exact controls; kernel rejects all eleven mutations")


if __name__ == "__main__":
    main()
