#!/usr/bin/env python3
"""Check signed packed words and require kernel rejection of changed data."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedSignedRun
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
open Tests.PackedSignedRun
namespace PackedXor9Control
'''


def main():
    controls = [
        ('packed borrow', 'PackedWordBounds.fastValid decreasing = true',
         'PackedWordBounds.fastValid crossBorrow = true'),
        ('packed high seed', 'PackedWordBounds.fastValid increasing = true',
         'PackedWordBounds.fastValid highSeed = true'),
        ('packed delta', 'PackedWordBounds.fastValid increasing = true',
         'PackedWordBounds.fastValid excessiveDelta = true'),
        ('negative endpoint', 'decreasing.valid 65536 = true', 'negativeEndpoint.valid 65536 = true'),
        ('large endpoint', 'increasing.valid 65536 = true', 'largeEndpoint.valid 65536 = true'),
        ('extra payload word', 'increasing.valid 65536 = true', 'extraWord.valid 65536 = true'),
        ('stride sign', 'PackedXor9Checks.check 512 [descendingBlock] = true',
         'PackedXor9Checks.check 512 [wrongStride] = true'),
        ('high bit', 'PackedXor9Checks.check 511 [crossingBlock] = true',
         'PackedXor9Checks.check 511 [wrongHighBit] = true'),
        ('domain end', 'PackedXor9Checks.check 262143 [lastBlock] = true',
         'PackedXor9Checks.check 262144 [lastBlock] = true'),
        ('source length', 'PackedXor9Checks.checkRequests requests = true',
         'PackedXor9Checks.checkRequests wrongSize = true'),
        ('source binding', '(Code.dense 2 66047).decode 65536 = Block.dense #[511, 1]',
         '(Code.dense 2 66047).decode 65536 = Block.dense #[255, 1]'),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            source = PREFIX + f'numeric_data_binding result : {statement}\nend PackedXor9Control\n'
            with tempfile.TemporaryDirectory(prefix='airbender-packed-xor9-') as directory:
                path = Path(directory) / 'Check.lean'
                path.write_text(source)
                result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n' + result.stdout[-2000:])
    print('PASS eleven exact results and bindings; kernel rejects all eleven mutations')


if __name__ == '__main__':
    main()
