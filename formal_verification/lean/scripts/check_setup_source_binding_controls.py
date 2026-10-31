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


def packed_binding_controls():
    for changed in (False, True):
        source = '''import Airbender.Import.PackedSetupEmbed
open Airbender.Setup Airbender.Compiler.PackedSetupEquality
namespace PackedBindingControl
setup_code_binding binding : ([Block.affine 1 0 0] : List Block) =
  [BlockCode.decode (.affine 1 NEXT 0)]
end PackedBindingControl
'''.replace('NEXT', '1' if changed else '0')
        with tempfile.TemporaryDirectory(prefix='airbender-packed-binding-') as directory:
            path = Path(directory) / 'Check.lean'
            path.write_text(source)
            result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=LEAN,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if not changed:
            if result.returncode != 0:
                raise SystemExit('Positive packed binding control failed:\n' + result.stdout[-3000:])
        elif result.returncode == 0:
            raise SystemExit('Kernel accepted a changed packed source binding')
        elif '(kernel) declaration type mismatch' not in result.stdout.lower():
            raise SystemExit('Packed binding failed for an unrelated reason:\n' + result.stdout[-3000:])
    print('PASS kernel accepts the exact packed binding and rejects a changed value')


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
    packed_binding_controls()


if __name__ == "__main__":
    main()
