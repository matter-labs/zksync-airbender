#!/usr/bin/env python3
"""Require kernel rejection of changed packed columns and reference spans."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedWordColumn
import Tests.ShiftPackedReference
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
open Tests.PackedWordColumn
open Airbender.Verification.ShiftPackedReference
namespace PackedWordColumnControl
'''


def main():
    controls = [
        ('length', 'column.check = true', 'badLength.check = true'),
        ('payload', 'column.check = true', 'badPayload.check = true'),
        ('extra word', 'column.check = true', 'extraPayload.check = true'),
        ('negative endpoint', 'first.check = true', 'negativeEndpoint.check = true'),
        ('empty block', 'first.check = true', 'emptyBlock.check = true'),
        ('source', 'first.blocks.map (Code.decode 65536) = [Block.affine 2 1 (-1)]',
         'first.blocks.map (Code.decode 65536) = [Block.affine 2 1 1]'),
        ('reference', 'column.checkReference (fun index => if index = 0 ∨ index = 3 then 1 else 0) 0 = true',
         'column.checkReference (fun _ => 0) 0 = true'),
        ('reference start', 'column.checkReference (fun index => if index = 0 ∨ index = 3 then 1 else 0) 0 = true',
         'column.checkReference (fun index => if index = 0 ∨ index = 3 then 1 else 0) 1 = true'),
        ('request start', '(column.requests 0).map Request.start = [0, 2]',
         '(column.requests 0).map Request.start = [0, 3]'),
        ('request count', '(column.requests 0).map Request.count = [2, 2]',
         '(column.requests 0).map Request.count = [2, 3]'),
        ('request payload', '(column.requests 0).map Request.payload = [1, 65536]',
         '(column.requests 0).map Request.payload = [1, 65537]'),
        ('numeric row binding', 'numericRow 0 896 = expectedRow 0 896',
         'numericRow 0 896 = expectedRow 0 897'),
        ('signed fill', 'checkSpan 0 229627 1 255 = true', 'checkSpan 0 229627 1 254 = true'),
        ('unsigned shift', 'checkSpan 0 98370 1 128 = true', 'checkSpan 0 98370 1 255 = true'),
        ('reverse byte', 'checkSpan 3 10757 1 42 = true', 'checkSpan 3 10757 1 0 = true'),
        ('invalid control', 'checkSpan 0 65284 1 0 = true', 'checkSpan 0 65284 1 42 = true'),
        ('last row', 'checkSpan 0 262143 1 0 = true', 'checkSpan 0 262144 1 0 = true'),
        ('span bound', 'checkSpan 0 0 1 0 = true', 'checkSpan 0 0 4097 0 = true'),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f'numeric_data_binding result : {statement}\nend PackedWordColumnControl\n'
            with tempfile.TemporaryDirectory(prefix='airbender-word-column-') as directory:
                path = Path(directory) / 'Check.lean'
                path.write_text(source)
                result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n' + result.stdout[-2000:])
    print('PASS eighteen exact results and bindings; kernel rejects all eighteen mutations')


if __name__ == '__main__':
    main()
