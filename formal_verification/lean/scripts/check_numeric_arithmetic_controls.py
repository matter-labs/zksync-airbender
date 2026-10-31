#!/usr/bin/env python3
"""Check exact numeric bindings and require kernel rejection after mutation."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler
namespace NumericBindingControl
numeric_polynomials polynomials from "Tests/fixtures/numeric-arithmetic.json" ["polynomials"]
numeric_combinations combinations from "Tests/fixtures/numeric-arithmetic.json" ["combinations"]
numeric_naturals keys from "Tests/fixtures/numeric-arithmetic.json" ["keys"]
'''


def main():
    controls = [
        ("coefficient", "polynomials", "[[(6, [0, 2]), (1, [])], []]", "[[(5, [0, 2]), (1, [])], []]"),
        ("variable", "polynomials", "[[(6, [0, 2]), (1, [])], []]", "[[(6, [0, 3]), (1, [])], []]"),
        ("certificate reference", "combinations", "[[([(1, [])], 3)], []]", "[[([(1, [])], 4)], []]"),
        ("address key", "keys", "[0, 2, 15]", "[0, 2, 16]"),
    ]
    for label, declaration, exact, changed in controls:
        for mutated, expression in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding bound : {declaration} = {expression}\nend NumericBindingControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-numeric-binding-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} binding failed:\n" + result.stdout[-2000:])
            if mutated:
                if not result.returncode:
                    raise SystemExit(f"Kernel accepted a changed {label}")
                if "(kernel) declaration type mismatch" not in result.stdout.lower():
                    raise SystemExit(f"Changed {label} failed for an unrelated reason:\n" + result.stdout[-2000:])
    for changed in (False, True):
        supplied = "True.intro" if changed else "native.full"
        source = """import Tests.NumericArithmeticChecks
import Airbender.Import.GKRProtocol.FullArithmeticCheckImport
open Airbender Airbender.Compiler
namespace NumericCorollaryControl
def native.addresses : List GKRAddress := [.BaseLayerWitness 0]
def native.artifact : ArithmeticExtension 1 1 Source.BaseField :=
  ⟨[atom 0], [.assertZero (.atom 0) (.atom 0)], id, atom⟩
def native.certificate : Certificate native.artifact.translation :=
  ⟨fun _ => [(constant 1, ⟨0, by decide⟩)], fun _ => [(constant 1, ⟨0, by decide⟩)]⟩
def native.gate0 : ArithmeticGate 1 Source.BaseField := .assertZero (.atom 0) (.atom 0)
theorem native.full : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true := by decide +kernel
certify_full_compiler_arithmetic native inputs 1 variables 1 sources 1 gates 1 using SUPPLIED
end NumericCorollaryControl
""".replace("SUPPLIED", supplied)
        with tempfile.TemporaryDirectory(prefix="airbender-numeric-corollary-") as directory:
            path = Path(directory) / "Check.lean"
            path.write_text(source)
            result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if not changed and result.returncode:
            raise SystemExit("Exact corollary control failed:\n" + result.stdout[-2000:])
        if changed and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
            raise SystemExit("Wrong corollary proof did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS five exact bindings and proofs; kernel rejects all five mutations")


if __name__ == "__main__":
    main()
