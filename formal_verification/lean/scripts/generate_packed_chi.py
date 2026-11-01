#!/usr/bin/env python3
"""Bind the complete native Chi output to one packed checker result."""
import argparse
import json
from pathlib import Path

from generate_packed_xor9 import block_length, term, ranges, tree, binding_tree

ROOT = Path(__file__).resolve().parents[1]


def native_blocks(artifact):
    region = next(table for table in artifact['tables'] if table['id'] == 39)
    if (region['length'], region['width'], region['key_columns']) != (65536, 3, 2):
        raise ValueError('Chi native region dimensions changed')
    position, blocks = 0, []
    start, end = region['offset'], region['offset'] + region['length']
    for block in artifact['columns'][2]['blocks']:
        length = block_length(block)
        if start <= position and position + length <= end:
            blocks.append(block)
        elif position < end and start < position + length:
            raise ValueError('Chi region boundary cuts a native block')
        position += length
    if sum(map(block_length, blocks)) != region['length']:
        raise ValueError('Chi capture does not cover its native region')
    return blocks


def generated(artifact):
    blocks = native_blocks(artifact)
    parts = ranges(0, len(blocks), 5)
    data = '''import Airbender.Proofs.Tables.PackedByteTableChecks
import Airbender.Data.Setup.Keccak.FixedData
import Airbender.Proofs.Tables.LiteralColumnParts
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Keccak.Proofs.ChiPackedCapture
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

literal_column_parts column from (chiData.columns[2]) depth 5

'''
    for index, (first, stop) in enumerate(parts):
        data += f'def blocks{index} : List Code := [' + ', '.join(map(term, blocks[first:stop])) + ']\n'
    data += '\ndef blocks : List Code := ' + tree([f'blocks{index}' for index in range(32)]) + '\n\n'
    for index in range(32):
        data += f'numeric_data_binding binding{index} : blocks{index}.map (Code.decode 65536) = columnBlocks{index}.toList\n'
    data += '\ntheorem source_binding : blocks.map (Code.decode 65536) = chiData.columns[2].blocks.toList := by\n'
    data += '  change blocks.map (Code.decode 65536) = column.blocks.toList\n'
    data += '  have joined : column.blocks = ' + tree([f'columnBlocks{i}' for i in range(32)]) + ' := rfl\n'
    data += '  rw [joined]\n  simpa only [blocks, List.map_append, Array.toList_append] using ' + binding_tree(0, 32) + '\n\n'
    data += 'end Airbender.Keccak.Proofs.ChiPackedCapture\n'
    certificate = '''import Airbender.Proofs.Keccak.ChiPackedCapture

namespace Airbender.Keccak.Proofs.ChiPackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .chi 0 blocks = true := by decide +kernel

end Airbender.Keccak.Proofs.ChiPackedCapture
'''
    public = '''import Airbender.Proofs.Keccak.ChiPackedCertificate

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem chi_output_checks :
    checkBlocks (fun n => (n % 256 ^^^ 255) &&& (n / 256)) 0
      chiData.columns[2].blocks.toList = true := by
  rw [← ChiPackedCapture.source_binding]
  exact PackedByteTableChecks.check_sound .chi 0 ChiPackedCapture.blocks ChiPackedCapture.checked

end Airbender.Keccak.Proofs
'''
    return {'Airbender/Proofs/Keccak/ChiPackedCapture.lean': data,
            'Airbender/Proofs/Keccak/ChiPackedCertificate.lean': certificate,
            'Airbender/Proofs/Keccak/ChiCertificate.lean': public}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = json.loads((ROOT / 'artifacts/setup/keccak.json').read_text())
    for relative, content in generated(artifact).items():
        path = ROOT / relative
        if not path.exists() or path.read_text() != content:
            if not args.write:
                raise ValueError('packed Chi output changed: ' + relative)
            path.write_text(content)
    print('PASS complete packed Chi capture')


if __name__ == '__main__':
    main()
