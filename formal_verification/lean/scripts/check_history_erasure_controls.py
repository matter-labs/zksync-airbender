#!/usr/bin/env python3
"""Reject changes to exact history substitutions and their complete source bindings."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from gkr_packed_history_erasure import CASES, dimensions


def compile_source(source):
    with tempfile.TemporaryDirectory(prefix='history-erasure-control-') as directory:
        path = Path(directory) / 'Check.lean'
        path.write_text(source)
        return subprocess.run(['lean', '--tstack=32768', '-j1', str(path)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericHistoryErasureChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender.Compiler NumericHistoryErasureChecks
namespace HistoryErasureControl
set_option maxRecDepth 8192
def tiny : Capture := ⟨[4],
  [([(1,[0]),(0,[])],[(1,[0]),(0,[])]), ([(1,[4])],[(0,[])]),
   ([(0,[4]),(1,[0])],[(0,[]),(1,[0])])],
  [([(1,[0]),(0,[])],[(1,[0]),(0,[])])]⟩
'''
    changes = [
        ('clock inverse', '(524288 : Source.BaseField) * 2013262081 = 1', '(524288 : Source.BaseField) * 2013262082 = 1', ''),
        ('unique coordinates', 'check 7 tiny = true', 'check 7 {tiny with coordinates := [4,4]} = true', ''),
        ('zero branch', 'check 7 tiny = true', 'check 7 {tiny with arithmetic := [([(1,[4])],[(1,[])])]} = true', ''),
        ('same branch', 'check 7 tiny = true', 'check 7 {tiny with arithmetic := [([(0,[4]),(1,[0])],[(1,[1])])]} = true', ''),
        ('field coefficient', 'check 7 tiny = true', 'check 7 {tiny with fields := [([(1,[0]),(0,[])],[(2,[0]),(0,[])])]} = true', ''),
        ('field coordinate', 'check 7 tiny = true', 'check 7 {tiny with fields := [([(1,[0]),(0,[])],[(1,[1]),(0,[])])]} = true', ''),
        ('zero term binding', 'tiny.fields = [([(1,[0]),(0,[])],[(1,[0]),(0,[])])]', 'tiny.fields = [([(1,[0])],[(1,[0]),(0,[])])]', ''),
    ] if not args.case else []
    for case in args.case or CASES:
        owner = 'Airbender.Compiler.HistoryErasureChecks.' + case
        native = 'Airbender.Compiler.HistoryErasureNative.' + case + '.native'
        base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
        source_model = 'Airbender.Compiler.SourceContractNative.' + case + '.native'
        source = (f'ofSource {native}.historyCells {source_model}.originals {source_model}.clock {base}.helperPlacement '
                  f'({native}.protectedFields.map (fun field => field.polynomial {base}.helperPlacement.memory))')
        for field in ['coordinates', 'arithmetic', 'fields']:
            changes.append((case + ' ' + field, f'{owner}.data = {source}',
                f'{{{owner}.data with «{field}» := {owner}.data.{field}.drop 1}} = {source}',
                'import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.' + case + '.Data\n'))
    for label, exact, changed, imports in changes:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement +
                                    '\nend HistoryErasureControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-2000:])
        print('PASS history control:', label, flush=True)
    print('PASS', len(changes), 'exact controls; kernel rejects all mutations', flush=True)
    if args.case:
        return
    opaque = compile_source('''import Airbender.Import.GKRProtocol.NumericHistoryErasureImport
open Airbender.Compiler
opaque hidden : NumericHistoryErasureChecks.Capture := ⟨[],[],[]⟩
numeric_history_erasure_capture rejected := hidden
''')
    if not opaque.returncode or 'did not reduce to closed numeric data' not in opaque.stdout:
        raise SystemExit('Opaque history payload was not rejected:\n' + opaque.stdout[-2000:])
    print('PASS opaque history payload rejection', flush=True)
    legacy = compile_source('''import Airbender.Import.GKRProtocol.HistoryErasureImport
import Airbender.Proofs.GKRProtocol.SourceContractNative.AddSubCached
open Airbender Airbender.Compiler
namespace HistoryErasureLegacy
set_option maxRecDepth 32768
import_history_erasure native from "artifacts/compiler/add-sub-cached-source.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native inputs 48
end HistoryErasureLegacy
''')
    if legacy.returncode:
        raise SystemExit('Legacy history importer failed:\n' + legacy.stdout[-2000:])
    print('PASS legacy history importer', flush=True)


if __name__ == '__main__':
    main()
