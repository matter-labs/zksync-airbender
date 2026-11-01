#!/usr/bin/env python3
"""Require kernel rejection of changes to byte-table operations and source data."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedByteTables
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks Tests.PackedByteTables
namespace PackedByteTableControl
'''


def main():
    controls = [
        ('operation', 'PackedByteTableChecks.check .chi 258 [chiByte] = true',
         'PackedByteTableChecks.check .bitXor 258 [chiByte] = true'),
        ('high byte', 'PackedByteTableChecks.check .chi 258 [chiByte] = true',
         'PackedByteTableChecks.check .chi 258 [highByte] = true'),
        ('stride', 'PackedByteTableChecks.check .chi 256 [descending] = true',
         'PackedByteTableChecks.check .chi 256 [.affine 2 1 1] = true'),
        ('final row', 'PackedByteTableChecks.check .chi 65535 [finalByte] = true',
         'PackedByteTableChecks.check .chi 65536 [finalByte] = true'),
        ('source binding', 'crossing.decode 65536 = Block.dense #[0, 1]',
         'crossing.decode 65536 = Block.dense #[1, 0]'),
        ('window', 'PackedByteTableChecks.legal 0 512 = true',
         'PackedByteTableChecks.legal 0 513 = true'),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f'numeric_data_binding result : {statement}\nend PackedByteTableControl\n'
            with tempfile.TemporaryDirectory(prefix='airbender-byte-table-') as directory:
                path = Path(directory) / 'Check.lean'
                path.write_text(source)
                result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n' + result.stdout[-2000:])
    print('PASS six exact results and bindings; kernel rejects all six mutations')


if __name__ == '__main__':
    main()
