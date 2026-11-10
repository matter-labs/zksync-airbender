#!/usr/bin/env python3
"""Require kernel rejection of changed finite-grid results and exact rotation bindings."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.FiniteGridChecks
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate8
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate16
import Airbender.Proofs.UnifiedReduced.Tables.RotateReferenceBytes
open Airbender Airbender.Compiler
namespace RotationControl
'''


def main():
    prefix = "Airbender.UnifiedReduced.Setup."
    reference = prefix + "Proofs."
    finite = "Airbender.Verification.FiniteGridChecks.check"
    controls = [
        ("finite final cell", f"{finite} 2 3 4 Tests.FiniteGridChecks.left Tests.FiniteGridChecks.right = true",
         f"{finite} 2 3 4 Tests.FiniteGridChecks.left Tests.FiniteGridChecks.wrong = true"),
        ("complete byte grid", f"{reference}rotationByteCheck = true",
         f"{finite} 4 4 256 (fun m l v => {reference}referenceRotatedByte m l v.val) (fun m l v => {reference}finiteRotatedByte m l v.val + 1) = true"),
        ("rotate8 binding", f"{prefix}nativeRotate8Data.columns[5].blocks = (Airbender.Blake2G.xor8Data.columns[2]'(by decide)).blocks",
         f"{prefix}nativeRotate8Data.columns[4].blocks = (Airbender.Blake2G.xor8Data.columns[2]'(by decide)).blocks"),
        ("rotate16 binding", f"{prefix}nativeRotate16Data.columns[4] = Airbender.Verification.byteXorData.columns[2]",
         f"{prefix}nativeRotate16Data.columns[4] = Airbender.Verification.byteXorData.columns[0]"),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding result : {statement}\nend RotationControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-rotation-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} failed:\n" + result.stdout[-2000:])
            if mutated and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
                raise SystemExit(f"Changed {label} did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS four exact bindings and results; kernel rejects all four mutations")


if __name__ == "__main__":
    main()
