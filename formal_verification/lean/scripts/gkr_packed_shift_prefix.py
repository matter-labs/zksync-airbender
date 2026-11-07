#!/usr/bin/env python3
"""Generate complete Shift prefix checks and exact source bindings."""
import argparse
import json
import re
from gkr_shift_prefix_instances import LEAN, modules as legacy_modules, plans

ADOPTED = tuple(range(10))


def capture(artifact, column):
    _, chunks = plans(artifact, column)
    stem = f'Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column{column}'
    owner = f'Airbender.Compiler.ShiftPrefixChecks.Column{column}'
    legacy = f'Airbender.Compiler.ShiftPrefixNative.Column{column}'
    header = (f'namespace {owner}\nopen Airbender Airbender.Compiler\n'
              'open PackedSetupEquality PackedSetupNormalization\n'
              'set_option warningAsError true\nset_option Elab.async false\n'
              'set_option maxRecDepth 131072\n\n')
    data = ('import Airbender.Import.GKRProtocol.BlockPartsImport\n'
            'import Airbender.Data.GKRSetup.ShiftBinop\nimport Airbender.Data.Tables.ShiftData\n\n'
            f'namespace {legacy}\nopen Airbender Airbender.Compiler\n'
            'set_option warningAsError true\nset_option Elab.async false\n'
            'set_option maxRecDepth 131072\n'
            '-- This command group names the complete imported column data.\n'
            'set_option maxHeartbeats 4000000\n\n')
    for _, source in legacy_modules(artifact, column):
        body = source[source.index('column_blocks_part original'):source.rindex('end ' + legacy)]
        body, count = re.subn(r'theorem chunkChecked\d+ :.*?\n\n', '', body, flags=re.S)
        body, lengths = re.subn(r'theorem chunkLength\d+ :.*?\n\n', '', body, flags=re.S)
        if count != lengths or not count:
            raise ValueError('legacy Shift facts changed')
        data += body
    data += 'end ' + legacy + '\n'
    yield stem + '.Data', data

    codes = (f'import {stem}.Data\nimport Airbender.Import.PackedSetupEmbed\n'
             'import Airbender.Proofs.GKRProtocol.PackedSetupNormalization\n\n' + header +
             '-- The importer reads the complete capture once. Each leaf has at most 128 blocks.\n'
             'set_option maxHeartbeats 4000000\n\n'
             'import_setup_code_capture from "artifacts/setup/shift-binop.json" [\n')
    specs, requests, region_requests = [], [], []
    for index, (first, last, lo, hi, selected) in enumerate(chunks):
        packing = 'packed_region 7' if column == 2 else 'unpacked'
        specs.append(f'  source{index} := column {column} block_start {first} block_count {last-first} {packing}')
        target_names = []
        for kind, start, end in selected:
            code = f'target{index}Region{kind}'
            region = artifact['tables'][kind]
            packed = int(region['id'] == 7 and column == 2)
            specs.append(f'  {code} := region {region["id"]} column {column} block_start {start} block_count {end-start} packed_bytes {packed}')
            target_names.append(code)
            rows = min(hi, region['offset'] + region['length']) - max(lo, region['offset'])
            region_requests.append((index, kind, code, rows))
        requests.append(f'⟨source{index}, ' + ' ++ '.join(target_names) + f', {hi-lo}⟩')
    requests += [f'⟨{code}, {code}, {rows}⟩' for _, _, code, rows in region_requests]
    codes += ',\n'.join(specs) + ']\n\n'
    codes += 'def requests : List Request := [\n  ' + ',\n  '.join(requests) + ']\n\nend ' + owner + '\n'
    yield stem + '.Codes', codes

    bindings = f'import {stem}.Codes\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header
    for index, (_, _, _, _, selected) in enumerate(chunks):
        bindings += (f'numeric_data_binding source{index}_binding : {legacy}.original{index} = source{index}.map BlockCode.decode\n'
                     f'numeric_data_binding target{index}_binding : {legacy}.target{index} = '
                     '(' + ' ++ '.join(f'target{index}Region{kind}' for kind, _, _ in selected) + ').map BlockCode.decode\n')
        for kind, _, _ in selected:
            code = f'target{index}Region{kind}'
            bindings += f'numeric_data_binding {code}_binding : {legacy}.{code} = {code}.map BlockCode.decode\n'
    bindings += '\nend ' + owner + '\n'
    yield stem + '.Bindings', bindings

    certificate = (f'import {stem}.Bindings\n\n' + header +
                   'theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel\n\n'
                   'theorem facts (index : Fin requests.length) : Fact (requests.get index) :=\n'
                   '  check_sound_at requests checked index\n\nend ' + owner + '\n')
    yield stem + '.Certificate', certificate

    projected = (f'import {stem}.Certificate\n\nnamespace {legacy}\nopen Airbender Airbender.Compiler\n'
                 'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    for index, _ in enumerate(chunks):
        projected += (f'theorem chunkChecked{index} : normalizeSetupBlocks original{index} = normalizeSetupBlocks target{index} := by\n'
                      f'  rw [{owner}.source{index}_binding, {owner}.target{index}_binding]\n'
                      f'  exact ({owner}.facts ⟨{index}, by decide +kernel⟩).1\n\n'
                      f'theorem chunkLength{index} : (original{index}.map Setup.Block.length).sum = {chunks[index][3]-chunks[index][2]} := by\n'
                      f'  rw [{owner}.source{index}_binding]\n'
                      f'  exact ({owner}.facts ⟨{index}, by decide +kernel⟩).2\n\n')
    for ordinal, (index, kind, code, rows) in enumerate(region_requests, len(chunks)):
        projected += (f'theorem checkedRegion{kind}Part{index}Length : ({code}.map Setup.Block.length).sum = {rows} := by\n'
                      f'  rw [{owner}.{code}_binding]\n'
                      f'  exact ({owner}.facts ⟨{ordinal}, by decide +kernel⟩).2\n\n')
    projected += 'end ' + legacy + '\n'
    yield stem + '.Projected', projected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column', action='append', type=int, choices=range(10))
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = json.loads((LEAN / 'artifacts/setup/shift-binop.json').read_text())
    for column in args.column if args.column is not None else ADOPTED:
        for name, source in capture(artifact, column):
            path = LEAN / (name.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != source):
                raise ValueError('complete Shift capture changed: ' + name)
            if args.write and (not path.exists() or path.read_text() != source):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            print(name)


if __name__ == '__main__':
    main()
