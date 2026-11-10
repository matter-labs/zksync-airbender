#!/usr/bin/env python3
"""Reject changes to every counter-frame check and its complete source binding."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from gkr_packed_counter_frame import CASES, dimensions


def compile_source(source):
    with tempfile.TemporaryDirectory(prefix='counter-frame-control-') as directory:
        path = Path(directory) / 'Check.lean'
        path.write_text(source)
        return subprocess.run(['lean', '--tstack=32768', '-j1', str(path)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericCounterFrameChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender.Compiler NumericCounterFrameChecks
namespace CounterFrameControl
set_option maxRecDepth 8192
def tiny : Capture := ⟨[10,11], [10,11], [4,5], [(20,20),(21,21)],
  [[(1,[0]),(0,[])]], [[(1,[1])]]⟩
'''
    changes = [
        ('exported columns', 'check 4 tiny = true', 'check 4 {tiny with exportedColumns := [10,12]} = true', ''),
        ('unique slots', 'check 4 tiny = true', 'check 4 {tiny with slots := [4,4]} = true', ''),
        ('fresh slots', 'check 4 tiny = true', 'check 5 tiny = true', ''),
        ('address return', 'check 4 tiny = true', 'check 4 {tiny with returns := [(20,20),(21,22)]} = true', ''),
        ('source coordinate', 'check 4 tiny = true', 'check 4 {tiny with source := [[(1,[4]),(0,[])]]} = true', ''),
        ('helper coordinate', 'check 4 tiny = true', 'check 4 {tiny with helpers := [[(1,[5])]]} = true', ''),
        ('zero term binding', 'tiny.source = [[(1,[0]),(0,[])]]', 'tiny.source = [[(1,[0])]]', ''),
    ] if not args.case else []
    for case in args.case or CASES:
        _, _, _, columns = dimensions(case)
        owner = 'Airbender.Compiler.CounterFrameChecks.' + case
        native = 'Airbender.Compiler.CounterFrameNative.' + case + '.native'
        base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
        table = 'Airbender.Compiler.TableNative.' + case + '.native'
        helper = 'Airbender.Compiler.HelperNative.' + case + '.native'
        source = (f'ofTyped {table}.multiplicityColumns {columns} {native}.slots {base}.inputBank '
                  f'{base}.artifact.source ({helper}.fields.map (fun field => field.polynomial {base}.helperPlacement))')
        for field in ['slots', 'source', 'helpers']:
            changes.append((case + ' ' + field, f'{owner}.data = {source}',
                f'{{{owner}.data with «{field}» := {owner}.data.{field}.drop 1}} = {source}',
                'import Airbender.Proofs.GKRProtocol.CounterFrameChecks.' + case + '.Data\n'))
    for label, exact, changed, imports in changes:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement +
                                    '\nend CounterFrameControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-2000:])
        print('PASS counter control:', label, flush=True)
    print('PASS', len(changes), 'exact controls; kernel rejects all mutations', flush=True)
    if args.case:
        return
    opaque = compile_source('''import Airbender.Import.GKRProtocol.NumericCounterFrameImport
open Airbender.Compiler
opaque hidden : NumericCounterFrameChecks.Capture := ⟨[],[],[],[],[],[]⟩
numeric_counter_frame_capture rejected := hidden
''')
    if not opaque.returncode or 'did not reduce to closed numeric data' not in opaque.stdout:
        raise SystemExit('Opaque counter payload was not rejected:\n' + opaque.stdout[-2000:])
    print('PASS opaque counter payload rejection', flush=True)
    legacy = compile_source('''import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.AddSubCached
import Airbender.Proofs.GKRProtocol.TableNative.AddSubCached
open Airbender Airbender.Compiler
namespace CounterFrameLegacy
import_counter_frame native from "artifacts/compiler/add-sub-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  table_model Airbender.Compiler.TableNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperNative.AddSubCached.native inputs 48
end CounterFrameLegacy
''')
    if legacy.returncode:
        raise SystemExit('Legacy counter importer failed:\n' + legacy.stdout[-2000:])
    print('PASS legacy counter importer', flush=True)


if __name__ == '__main__':
    main()
