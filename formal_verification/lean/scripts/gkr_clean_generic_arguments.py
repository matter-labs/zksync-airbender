#!/usr/bin/env python3
"""Kernel-bind each retained generic lookup argument to its native source field."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def modules(name, case):
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    queries = pair['circuit']['generic_lookups']
    if not queries:
        return
    cert = json.loads((LEAN / 'artifacts/compiler/lookup' / (name + '.json')).read_text())
    rows = {row['native_index']: row for row in cert['rows'] if row['kind'] == 'generic'}
    if set(rows) != set(range(len(queries))):
        raise ValueError('generic query coverage changed: ' + name)
    namespace = 'Airbender.Compiler.CleanGenericArgumentsNative.' + case + '.native'
    header = (f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
              'set_option warningAsError true\nset_option Elab.async false\n'
              'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n')
    parts = []
    for start in range(0, len(queries), 8):
        target = 'GKRProtocol.CleanGenericArgumentsParts.' + case + '.Part' + str(start // 8)
        parts.append(target)
        text = ('import GKRProtocol.CleanGenericArgumentsImport\n'
                f'import GKRProtocol.CleanArithmeticNative.{case}\n'
                f'import GKRProtocol.FunctionalLinksNative.{case}\n\n' + header +
                f'import_clean_generic_arguments part{start // 8} from "artifacts/compiler/{name}.json"\n'
                f'  certificate "artifacts/compiler/lookup/{name}.json"\n')
        for key, model in [('clean_model', 'CleanArithmeticNative'), ('base_model', 'FullArithmeticNative'),
                           ('lookup_model', 'LookupNative'), ('query_model', 'LookupSourceNative'),
                           ('links_model', 'FunctionalLinksNative')]:
            text += f'  {key} Airbender.Compiler.{model}.{case}.native\n'
        text += f'  start {start} stop {min(start + 8, len(queries))}\n\nend {namespace}\n'
        yield target, text
    text = ''.join('import ' + part + '\n' for part in parts) + '\n' + header
    names = []
    for index, query in enumerate(queries):
        source_index = rows[index]['source_index']
        stem = f'genericExpressions{index}'
        entries = ', '.join(f'part{index // 8}.genericExpression{source_index}_{column}'
                            for column in range(len(query['columns'])))
        text += (f'noncomputable def {stem} : Vector (_root_.Expression Source.BaseField) {len(query["columns"])} :=\n'
                 f'  #v[{entries}]\n\n')
        names.append(stem)
    width = pair['circuit']['generic_lookup_tables_width']
    text += (f'noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) {width}) :=\n'
             '  [' + ', '.join(names) + ']\n\n' + f'end {namespace}\n')
    yield 'GKRProtocol.CleanGenericArgumentsNative.' + case, text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            name, case = family + '-' + mode, stem + mode.title()
            for target, text in modules(name, case):
                path = LEAN / (target.replace('.', '/') + '.lean')
                if args.check and (not path.exists() or path.read_text() != text):
                    raise ValueError('retained generic argument binding changed: ' + target)
                if args.write and (not path.exists() or path.read_text() != text):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text)
                print(target, flush=True)
                if args.build:
                    subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                                   env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
