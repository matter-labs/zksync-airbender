#!/usr/bin/env python3
"""Require kernel rejection of false terminal-block and padding bounds."""

import subprocess
import tempfile
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]


def check():
    for label, first, length, cutoff, accepted in [
        ("valid", 0, 4, 0, True),
        ("nonzero", 1, 4, 0, False),
        ("short", 0, 5, 0, False),
    ]:
        source = f'''import Airbender.Proofs.FullUnsigned.SetupSourceTails
namespace PaddingControl
open Airbender.Setup
private def binding : SourceBank.ColumnBinding :=
  ⟨0, 0, 0, id, fun _ => .affine 4 {first} 0, [0]⟩
private def storedColumn : Column := binding.column
noncomputable def columnBindings : List (SourceBank.ColumnBinding × Column) :=
  [(binding, storedColumn)]
def column (_ : Nat) : Column := storedColumn
def columnsEntries : List Nat := [0]
def columns : Array Column := (columnsEntries.map column).toArray
end PaddingControl
certify_source_tails PaddingControlProofs using PaddingControl
  trace_rows {length} padding_start {cutoff}
'''
        with tempfile.TemporaryDirectory(prefix="airbender-padding-control-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            result = subprocess.run(
                ["lean", "-j1", "-DElab.async=false", str(path)], cwd=LEAN,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
        if accepted:
            if result.returncode:
                raise RuntimeError(f"Valid padding control failed:\n{result.stdout[-4000:]}")
        elif result.returncode == 0 or not any(marker in result.stdout for marker in [
            "type mismatch", "Type mismatch", "Application type mismatch", "declaration has metavariables",
        ]):
            raise RuntimeError(f"False padding control did not fail as expected:\n{result.stdout[-4000:]}")
    print("PASS padding controls: valid accepted; nonzero tail and short padding rejected")


if __name__ == "__main__":
    check()
