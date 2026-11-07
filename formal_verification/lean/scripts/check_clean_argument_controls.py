#!/usr/bin/env python3
"""Check exact Clean argument rows, original ports and complete source bindings."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from gkr_packed_clean_arguments import CASES, descriptors, scalar_commands, generic_command


def compile_source(source):
    with tempfile.TemporaryDirectory(prefix='clean-argument-control-') as directory:
        path = Path(directory) / 'Check.lean'
        path.write_text(source)
        return subprocess.run(['lean', '--tstack=32768', '-j1', str(path)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender.Compiler NumericFunctionalBaseChecks
namespace CleanArgumentControl
set_option maxRecDepth 8192
def tiny : Data := ⟨[(20,20,1)],[(1,[0]),(0,[])],[(1,[0]),(0,[])]⟩
'''
    changes = [
        ('address return', 'check 7 [tiny] = true', 'check 7 [{tiny with ports := [(21,20,1)]}] = true', ''),
        ('port flag', 'check 7 [tiny] = true', 'check 7 [{tiny with ports := [(20,20,0)]}] = true', ''),
        ('polynomial coefficient', 'check 7 [tiny] = true', 'check 7 [{tiny with right := [(2,[0]),(0,[])]}] = true', ''),
        ('polynomial coordinate', 'check 7 [tiny] = true', 'check 7 [{tiny with right := [(1,[1]),(0,[])]}] = true', ''),
        ('zero term binding', 'tiny.left = [(1,[0]),(0,[])]', 'tiny.left = [(1,[0])]', ''),
    ] if not args.case else []
    for case in args.case or CASES:
        owner = 'Airbender.Compiler.CleanArgumentChecks.' + case
        count = len(descriptors(case))
        for first in [0, count - 1]:
            left = f'({owner}.data.drop {first}).take 1'
            right = f'(({owner}.originalEntries.drop {first}).take 1).map encode'
            changes.append((case + ' ' + str(first), left + ' = ' + right, '(' + left + ').drop 1 = ' + right,
                            'import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.' + case + '.Data\n'))
        if count >= 32:
            for first in [0, (count - 1) // 8 * 8]:
                width = min(8, count - first)
                left = f'({owner}.originalEntries.drop {first}).take {width}'
                right = f'{owner}.entries{first}'
                changes.append((case + ' projection ' + str(first), left + ' = ' + right,
                    left + ' = (' + right + f').drop {width}',
                    'import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.' + case + '.Certificate\n'))
    for label, exact, changed, imports in changes:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement +
                                    '\nend CleanArgumentControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-2000:])
        print('PASS Clean argument control:', label, flush=True)
    print('PASS', len(changes), 'exact controls; kernel rejects all mutations', flush=True)
    if args.case:
        return
    legacy = '''import Airbender.Import.GKRProtocol.CleanLookupArgumentsImport
import Airbender.Import.GKRProtocol.CleanHelperArgumentsImport
import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.WordMemoryCached
namespace CleanArgumentLegacy
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
'''
    legacy += scalar_commands('WordMemoryCached', 0).replace(' phase 0', '') + '\n'
    legacy += generic_command('WordMemoryCached', 0).replace(' part_size 8 phase 0', '')
    legacy += '\nend CleanArgumentLegacy\n'
    result = compile_source(legacy)
    if result.returncode:
        raise SystemExit('Legacy Clean argument importers failed:\n' + result.stdout[-2000:])
    print('PASS all three legacy Clean argument importers', flush=True)


if __name__ == '__main__':
    main()
