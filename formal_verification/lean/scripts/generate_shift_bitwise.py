#!/usr/bin/env python3
"""Bind the complete native OR and XOR outputs to proved byte checkers."""
import argparse
import json
from pathlib import Path

from generate_packed_xor9 import block_length, term, ranges, tree, binding_tree
from gkr_unified_prefix import slice_block

ROOT = Path(__file__).resolve().parents[1]


def native_blocks(artifact, tag):
    region = next(table for table in artifact['tables'] if table['id'] == tag)
    if (region['length'], region['width'], region['key_columns']) != (65536, 3, 2):
        raise ValueError('bitwise native region dimensions changed')
    position, blocks = 0, []
    for block in artifact['columns'][2]['blocks']:
        length = block_length(block)
        first = max(region['offset'], position)
        last = min(region['offset'] + region['length'], position + length)
        if first < last:
            blocks.extend(selected for _, selected in slice_block(block, first - position, last - first))
        position += length
    if sum(map(block_length, blocks)) != region['length']:
        raise ValueError('incomplete bitwise native region')
    return blocks


def generated(artifact, blake_artifact):
    result = {}
    for name, tag, operation, symbol in [('Or', 6, 'bitOr', '|||'), ('Xor', 4, 'bitXor', '^^^'), ('BlakeXor8', 4, 'bitXor', '^^^')]:
        is_blake = name == 'BlakeXor8'
        selected = blake_artifact if is_blake else artifact
        blocks = native_blocks(selected, tag)
        parts = ranges(0, len(blocks), 5)
        namespace = ('Airbender.Blake2G.Proofs.Xor8PackedCapture' if is_blake else
                     'Airbender.Verification.ShiftCertificate.' + name + 'PackedCapture')
        base = 'Airbender/Proofs/Blake2G/Xor8' if is_blake else 'Airbender/Proofs/Tables/Shift' + name
        module = base.replace('/', '.')
        data_import = 'Airbender.Data.Setup.Blake2G.XorData' if is_blake else 'Airbender.Data.Tables.Shift.' + name + 'Data'
        column = "(Airbender.Blake2G.xor8Data.columns[2])" if is_blake else f'byte{name}Data.columns[2]'
        public_column = "(xor8Data.columns[2]'(by omega))" if is_blake else column
        public_namespace = 'Airbender.Blake2G.Proofs.XorCertificate' if is_blake else 'Airbender.Verification.ShiftCertificate'
        public_name = 'output8' if is_blake else name.lower() + '_outputs'
        capture_name = 'Xor8PackedCapture' if is_blake else name + 'PackedCapture'
        data = f'''import Airbender.Proofs.Tables.PackedByteTableChecks
import {data_import}
import Airbender.Proofs.Tables.LiteralColumnParts
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace {namespace}
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

literal_column_parts column from ({column}) depth 5

'''
        for index, (first, stop) in enumerate(parts):
            data += f'def blocks{index} : List Code := [' + ', '.join(map(term, blocks[first:stop])) + ']\n'
        data += '\ndef blocks : List Code := ' + tree([f'blocks{i}' for i in range(32)]) + '\n\n'
        for index in range(32):
            data += f'numeric_data_binding binding{index} : blocks{index}.map (Code.decode 65536) = columnBlocks{index}.toList\n'
        data += f'\ntheorem source_binding : blocks.map (Code.decode 65536) = {column}.blocks.toList := by\n'
        data += '  change blocks.map (Code.decode 65536) = column.blocks.toList\n'
        data += '  have joined : column.blocks = ' + tree([f'columnBlocks{i}' for i in range(32)]) + ' := rfl\n'
        data += '  rw [joined]\n  simpa only [blocks, List.map_append, Array.toList_append] using ' + binding_tree(0, 32) + '\n\n'
        data += f'end {namespace}\n'
        certificate = f'''import {module}PackedCapture

namespace {namespace}
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .{operation} 0 blocks = true := by decide +kernel

end {namespace}
'''
        extra = 'import Airbender.Proofs.Blake2G.Xor8Certificate\n' if name == 'Xor' else ''
        public = f'''import {module}PackedCertificate
{extra}
namespace {public_namespace}
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem {public_name} :
    checkBlocks (fun n => n / 256 {symbol} n % 256) 0
      {public_column}.blocks.toList = true := by
  rw [← {capture_name}.source_binding]
  exact PackedByteTableChecks.check_sound .{operation} 0 {capture_name}.blocks {capture_name}.checked

end {public_namespace}
'''
        result[base + 'PackedCapture.lean'] = data
        result[base + 'PackedCertificate.lean'] = certificate
        result[base + 'Certificate.lean'] = public
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = json.loads((ROOT / 'artifacts/setup/shift-binop.json').read_text())
    blake_artifact = json.loads((ROOT / 'artifacts/setup/blake-g.json').read_text())
    for relative, content in generated(artifact, blake_artifact).items():
        path = ROOT / relative
        if not path.exists() or path.read_text() != content:
            if not args.write:
                raise ValueError('packed bitwise capture changed: ' + relative)
            path.write_text(content)
    print('PASS complete native OR, XOR and Blake byte-XOR captures')


if __name__ == '__main__':
    main()
