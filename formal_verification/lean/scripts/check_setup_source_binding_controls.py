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
    for changed in (False, True):
        source = """import Airbender.Import.PackedSetupEmbed
open Airbender.Setup Airbender.Compiler.PackedSetupEquality
namespace BalancedBindingControl
def first : List Block := [.affine 1 0 0]
def second : List Block := [.affine 1 3 0]
def firstCode : List BlockCode := [.affine 1 0 0]
def secondCode : List BlockCode := [.affine 1 NEXT 0]
setup_code_binding binding : List.append first second =
  (List.append firstCode secondCode).map BlockCode.decode
end BalancedBindingControl
""".replace('NEXT', '4' if changed else '3')
        with tempfile.TemporaryDirectory(prefix='airbender-balanced-binding-') as directory:
            path = Path(directory) / 'Check.lean'
            path.write_text(source)
            result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=LEAN,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if not changed and result.returncode != 0:
            raise SystemExit('Positive balanced binding control failed:\n' + result.stdout[-3000:])
        if changed:
            if result.returncode == 0:
                raise SystemExit('Kernel accepted a changed balanced source binding')
            if '(kernel)' not in result.stdout.lower() or 'type mismatch' not in result.stdout.lower():
                raise SystemExit('Balanced binding failed for an unrelated reason:\n' + result.stdout[-3000:])
    for changed in (False, True):
        source = """import Airbender.Import.GKRProtocol.BlockCoverageImport
open Airbender.Setup Airbender.Compiler.BlockCoverageImport
namespace LayoutBindingControl
def first : List Block := [.affine 1 0 0, .affine 1 1 0]
def second : List Block := [.affine 1 2 0, .affine 1 NEXT 0]
def part : List Block := List.append first second
def fixtureColumn : Column := ⟨([.affine 1 0 0, .affine 1 1 0,
  .affine 1 2 0, .affine 1 3 0] : List Block).toArray⟩
column_parts_cover binding from fixtureColumn parts [part]
end LayoutBindingControl
""".replace('NEXT', '4' if changed else '3')
        with tempfile.TemporaryDirectory(prefix='airbender-layout-binding-') as directory:
            path = Path(directory) / 'Check.lean'
            path.write_text(source)
            result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=LEAN,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if not changed and result.returncode != 0:
            raise SystemExit('Positive layout binding control failed:\n' + result.stdout[-3000:])
        if changed:
            if result.returncode == 0:
                raise SystemExit('Kernel accepted a changed layout source binding')
            if '(kernel)' not in result.stdout.lower() or 'type mismatch' not in result.stdout.lower():
                raise SystemExit('Layout binding failed for an unrelated reason:\n' + result.stdout[-3000:])
    print('PASS exact flat, balanced and layout bindings; kernel rejects each changed value')


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
