#!/usr/bin/env python3
"""Require kernel rejection of changed Clean ideal data and certificates."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.CleanIdealChecks
import Tests.CleanIdealTrace
import Tests.CleanIdealRows
open Airbender Airbender.Compiler
namespace CleanIdealControl
'''


def main():
    checker = "Airbender.Compiler.CleanIdealChecks.check 7"
    tests = "Tests.CleanIdealChecks."
    controls = [(label, f"{checker} {tests}capture = true", f"{checker} {tests}{name} = true")
                for label, name in [("code", "wrongCode"), ("coefficient", "wrongCoefficient"),
                    ("empty witness", "emptyWitness"), ("relation index", "outsideRelation"),
                    ("scope", "outsideScope"), ("missing witness", "missingWitness"),
                    ("forged size", "wrongBranchSize")]]
    controls += [
        ("source binding", f"CleanIdealChecks.encode {tests}placement {tests}expression = {tests}capture.codes.getD 0 (.constant 0)",
         f"CleanIdealChecks.encode {tests}placement {tests}expression = {tests}wrongCode.codes.getD 0 (.constant 0)"),
        ("relation binding", f"{tests}relations.map NumericPolynomialChecks.encode = {tests}capture.relations.toList",
         f"{tests}relations.map NumericPolynomialChecks.encode = {tests}wrongCoefficient.relations.toList"),
        ("witness binding", f"NumericPolynomialChecks.encodeCombination ({tests}witnesses.getD 0 []) = {tests}capture.witnesses.getD 0 []",
         f"NumericPolynomialChecks.encodeCombination ({tests}witnesses.getD 0 []) = {tests}emptyWitness.witnesses.getD 0 []"),
    ]
    trace_tests = "Tests.CleanIdealTrace."
    controls += [(label, f"Airbender.Compiler.CleanIdealTrace.{method} 7 {trace_tests}capture = true",
                  f"Airbender.Compiler.CleanIdealTrace.{method} 7 {trace_tests}{name} = true")
                 for label, method, name in [("missing trace rows", "bindingCheck", "missingRows"),
                    ("missing normal form", "check", "missingNormal"),
                    ("changed normal form", "bindingCheck", "wrongNormal"),
                    ("changed trace state", "check", "wrongTrace")]]
    row_tests = "Tests.CleanIdealRows."
    controls += [(label, f"Airbender.Compiler.CleanIdealRows.check 7 {row_tests}capture = true",
                  f"Airbender.Compiler.CleanIdealRows.check 7 {row_tests}{name} = true")
                 for label, name in [("changed expansion", "wrongExpanded"), ("changed combination", "wrongCombination")]]
    controls += [("exact expansion binding",
        f"CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial 7) {row_tests}capture.ideals.codes = {row_tests}capture.expanded",
        f"CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial 7) {row_tests}capture.ideals.codes = {row_tests}wrongExpanded.expanded")]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f"numeric_data_binding result : {statement}\nend CleanIdealControl\n"
            with tempfile.TemporaryDirectory(prefix="airbender-clean-ideal-") as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(source)
                result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f"Exact {label} failed:\n" + result.stdout[-2000:])
            if mutated and (not result.returncode or "(kernel) declaration type mismatch" not in result.stdout.lower()):
                raise SystemExit(f"Changed {label} did not fail in the kernel:\n" + result.stdout[-2000:])
    print("PASS seventeen exact bindings and results; kernel rejects all seventeen mutations")


if __name__ == "__main__":
    main()
