#!/usr/bin/env python3
"""Generate complete fixed-column captures and exact native bindings."""
import argparse
from export_gkr_translations import LEAN
from gkr_unified_prefix import CHUNK, DATA, plans

COLUMNS = (4, 6, 7)
BASE = LEAN / 'Airbender/Proofs/GKRProtocol/UnifiedPackedEquality'


def joined(values):
    return ' ++ '.join(values) if values else '[]'


def capture_plan(column):
    artifact, blocks, positions, stop, groups, regions = plans(column)
    selected = [(first, min(first + CHUNK, stop)) for first in range(0, stop, CHUNK)
                if all(entry['mode'] == 'identical' for group in groups[first:min(first + CHUNK, stop)] for entry in group)]
    spans = []
    for first, last in selected:
        if last - first != CHUNK:
            raise ValueError('fixed tree leaf width changed')
        if spans and spans[-1][1] == first:
            spans[-1][1] = last
        else:
            spans.append([first, last])
    targets = []
    for region_index, region in enumerate(artifact['tables']):
        indexes = [entry['target'] for first, last in selected for group in groups[first:last]
                   for entry in group if entry['region'] == region_index]
        if not indexes:
            continue
        if region['id'] not in (9, 47, 48):
            raise ValueError('unexpected region in fixed tree capture')
        if indexes != list(range(indexes[0], indexes[-1] + 1)):
            raise ValueError('fixed target span is not contiguous')
        field = DATA[region['id']]
        label = field.removeprefix('native').removesuffix('Data')
        targets.append((region['id'], label, field, indexes[0], indexes[-1] + 1, len(regions[region_index])))
    checks, offset = [], 0
    for first, last in selected:
        checks.append((offset, last - first, positions[last] - positions[first]))
        offset += last - first
    if offset != sum(last - first for _, _, _, first, last, _ in targets):
        raise ValueError('fixed source and target widths differ')
    return len(blocks), spans, targets, checks


def modules(column):
    total, spans, targets, checks = capture_plan(column)
    namespace = f'Airbender.Compiler.UnifiedPackedEquality.Column{column}'
    stem = f'Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column{column}'
    source_column = f'Data.GKRSetup.Unified.setupColumn{column}'
    sources = [f'({source_column}.blocks.toList.drop {first}).take {last-first}' for first, last in spans]
    target_columns = [f'(UnifiedReduced.Setup.{field}.columns[({column} : Nat)])' for _, _, field, _, _, _ in targets]
    target_views = [f'({col}.blocks.toList.drop {first}).take {last-first}' for col, (_, _, _, first, last, _) in zip(target_columns, targets)]
    header = f'namespace {namespace}\nopen Airbender Airbender.Compiler.PackedSetupEquality\nset_option warningAsError true\n'
    codes = ('import Airbender.Import.PackedSetupEmbed\nimport Airbender.Data.GKRSetup.Unified\n' +
             ''.join(f'import Airbender.Data.Setup.UnifiedReduced.Native.{label}Data\n' for _, label, _, _, _, _ in targets) + '\n' + header +
             'set_option Elab.async false\nset_option maxRecDepth 131072\n'
             '-- The complete native capture and its append layouts use bounded data.\n'
             'set_option maxHeartbeats 4000000\n\nimport_setup_code_capture from "artifacts/setup/unified.json" [\n')
    requests = [f'  source{index} := column {column} block_start {first} block_count {last-first} packed_region 54' for index, (first, last) in enumerate(spans)]
    requests += [f'  {label.lower()}Code := region {region} column {column} block_start {first} block_count {last-first} packed_bytes 0' for region, label, _, first, last, _ in targets]
    codes += ',\n'.join(requests) + ']\n\n'
    codes += 'def sourceCode : List BlockCode := ' + joined([f'source{i}' for i in range(len(spans))]) + '\n'
    codes += 'def targetCode : List BlockCode := ' + joined([label.lower()+'Code' for _, label, _, _, _, _ in targets]) + '\n\n'
    codes += ('setup_code_tree sourceTree from sourceCode => source_tree_binding\n'
              'setup_code_tree targetTree from targetCode => target_tree_binding\n\n'
              'def lengthChecks : List LengthCheck := [\n' + ',\n'.join(f'  ⟨{first}, {count}, {rows}⟩' for first, count, rows in checks) + ']\n\nend ' + namespace + '\n')
    yield 'Codes', codes

    bindings = f'import {stem}.Codes\nimport Airbender.Import.GKRProtocol.BlockCoverageImport\n\n' + header
    bindings += ('set_option Elab.async false\nset_option maxRecDepth 131072\n'
                 '-- Bind the complete fixed spans to the native columns.\nset_option maxHeartbeats 4000000\n\n')
    parts, source_parts = [], []
    position = 0
    for index, (first, last) in enumerate(spans):
        if position < first:
            name = 'rawPrefix' if index == 0 else f'rawGap{index}'
            parts.append((name, position, first))
        name = f'rawSource{index}'
        parts.append((name, first, last)); source_parts.append(name)
        position = last
    if position < total:
        parts.append(('rawSuffix', position, total))
    for name, first, last in parts:
        bindings += f'column_blocks_part {name} from {source_column} start {first} stop {last}\n'
    bindings += f'column_parts_cover sourceLayout from {source_column} parts ['+', '.join(name for name, _, _ in parts)+']\n\n'
    for index, name in enumerate(source_parts):
        bindings += f'setup_code_binding raw_source{index}_binding : {name} = source{index}.map BlockCode.decode\n'
    bindings += f'\nprivate theorem source_shape : {source_column}.blocks.toList = '+joined([name for name, _, _ in parts])+ ' := by\n'
    bindings += '  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using sourceLayout\n\n'
    for index, (first, last) in enumerate(spans):
        middle = next(i for i, part in enumerate(parts) if part[0] == source_parts[index])
        front = joined([name for name, _, _ in parts[:middle]])
        tail = joined([name for name, _, _ in parts[middle+1:]])
        bindings += (f'theorem source{index}_binding : {sources[index]} = source{index}.map BlockCode.decode := by\n'
                     f'  apply Eq.trans _ raw_source{index}_binding\n'
                     f'  apply select_middle _ ({front}) {source_parts[index]} ({tail}) {first} {last-first}\n'
                     '  · simpa only [List.append_assoc] using source_shape\n  · decide +kernel\n  · decide +kernel\n\n')
    bindings += f'theorem source_binding : {joined(sources)} = sourceCode.map BlockCode.decode := by\n'
    bindings += '  rw ['+', '.join(f'source{i}_binding' for i in range(len(spans)))+']\n  simp only [sourceCode'+(', List.map_append' if len(spans)>1 else '')+']\n\n'
    for col, (_, label, field, first, last, size) in zip(target_columns, targets):
        parts = []
        if first:
            parts.append((f'raw{label}Prefix', 0, first))
        parts.append((f'raw{label}', first, last))
        if last < size:
            parts.append((f'raw{label}Suffix', last, size))
        for name, start, end in parts:
            bindings += f'column_blocks_part {name} from {col} start {start} stop {end}\n'
        tag = label.lower()
        bindings += f'column_parts_cover {tag}Layout from {col} parts ['+', '.join(name for name, _, _ in parts)+']\n'
        bindings += f'setup_code_binding raw_{tag}_binding : raw{label} = {tag}Code.map BlockCode.decode\n\n'
        front = f'raw{label}Prefix' if first else '[]'
        tail = f'raw{label}Suffix' if last < size else '[]'
        bindings += (f'theorem {tag}_binding : ({col}.blocks.toList.drop {first}).take {last-first} = {tag}Code.map BlockCode.decode := by\n'
                     f'  apply Eq.trans _ raw_{tag}_binding\n  apply select_middle _ {front} raw{label} {tail} {first} {last-first}\n'
                     f'  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.append_assoc] using {tag}Layout\n'
                     '  · decide +kernel\n  · decide +kernel\n\n')
    bindings += f'theorem target_binding : {joined(target_views)} = targetCode.map BlockCode.decode := by\n'
    bindings += '  rw ['+', '.join(label.lower()+'_binding' for _, label, _, _, _, _ in targets)+']\n  simp only [targetCode'+(', List.map_append' if len(targets)>1 else '')+']\n\nend '+namespace+'\n'
    yield 'Bindings', bindings

    template = (BASE/'Column5/Certificate.lean').read_text().split('theorem fixed_column_blocks :')[0]
    certificate = template.replace('Column5', f'Column{column}').replace('26,112 records and their 204 row counts', f'{sum(count for _, count, _ in checks):,} records and their {len(checks)} row counts')
    certificate += (f'theorem fixed_column_blocks : {joined(sources)} = {joined(target_views)} := by\n'
                    '  rw [source_binding, target_binding]\n  exact blocks_eq\n\n'
                    'theorem row_counts (item : LengthCheck) (member : item ∈ lengthChecks) :\n'
                    f'    (((({joined(sources)}).drop item.first).take item.count).map Setup.Block.length).sum = item.expected := by\n'
                    '  rw [source_binding]\n  exact checked_facts.2 item member\n\nend '+namespace+'\n')
    yield 'Certificate', certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column', type=int, choices=COLUMNS, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for column in args.column or COLUMNS:
        for part, text in modules(column):
            path = BASE/f'Column{column}/{part}.lean'
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('packed fixed capture changed: '+str(path))
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(path.relative_to(LEAN))


if __name__ == '__main__':
    main()
