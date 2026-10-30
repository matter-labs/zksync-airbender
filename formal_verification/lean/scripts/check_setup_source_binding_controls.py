#!/usr/bin/env python3
"""Require the kernel to reject a changed retained RLE block binding."""

import subprocess
import tempfile
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
SOURCE = '''import Airbender.Data.Setup.Source.ParityRLE
import Airbender.Proofs.FullUnsigned.SetupSourceCertificate
namespace RejectedRleData
open Airbender.Setup
'''
ORIGINAL = "Airbender.Setup.SourceCaptureParity."
for field in ("text", "token", "bank", "fuel", "naturalSources", "valueArrays", "blockArrays",
              "columnBindings", "root", "column",
              "columnsIndex", "columnsChildren", "columnsEntries", "columns", "traceLength"):
    SOURCE += f"noncomputable def {field} := {ORIGINAL}{field}\n"
SOURCE += f'''noncomputable def blockSources : List (Nat × Block) :=
  match {ORIGINAL}blockSources with
  | [] => []
  | (index, _) :: rest => (index, .affine 0 0 0) :: rest
end RejectedRleData
certify_source_rle RejectedRleProofs using RejectedRleData
'''


def main():
    with tempfile.TemporaryDirectory(prefix="airbender-rle-rejection-") as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(SOURCE)
        result = subprocess.run(["lean", "-j1", "-DElab.async=false", str(path)], cwd=LEAN,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        output = result.stdout
        if result.returncode == 0:
            raise SystemExit("Kernel accepted a changed retained RLE block")
        if "type mismatch" not in output.lower() or not any(
                marker in output for marker in ("BlockAt", "rle_block_")):
            raise SystemExit("RLE rejection control failed for an unrelated reason:\n" + output[-3000:])
    print("PASS kernel rejects a changed retained RLE block binding")


if __name__ == "__main__":
    main()
