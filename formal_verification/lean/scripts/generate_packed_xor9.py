#!/usr/bin/env python3
"""Pack the complete native XOR9 capture and preserve its public corollaries."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = 'Airbender/Proofs/Blake2G'
PREFIX = 'Airbender.Blake2G.Proofs'


def block_length(block):
    if block['kind'] == 'affine':
        return block['length']
    return len(block['values']) * (block['repetitions'] if block['kind'] == 'periodic' else 1)


def native_blocks(artifact):
    region = next(table for table in artifact['tables'] if table['id'] == 20)
    if (region['length'], region['width'], region['key_columns']) != (262144, 3, 2):
        raise ValueError('XOR9 native region dimensions changed')
    position, blocks = 0, []
    start, end = region['offset'], region['offset'] + region['length']
    for block in artifact['columns'][2]['blocks']:
        length = block_length(block)
        if start <= position and position + length <= end:
            blocks.append(block)
        elif position < end and start < position + length:
            raise ValueError('XOR9 region boundary cuts a native block')
        position += length
    if sum(map(block_length, blocks)) != region['length']:
        raise ValueError('XOR9 capture does not cover its native region')
    return blocks


def pack(values):
    if any(not 0 <= value < 65536 for value in values):
        raise ValueError('XOR9 payload exceeds a packed word')
    return sum(value << (16 * index) for index, value in enumerate(values))


def term(block):
    if block['kind'] == 'affine':
        return f"(.affine {block['length']} {block['first']} ({block['step']}))"
    if block['kind'] == 'dense':
        return f"(.dense {len(block['values'])} {pack(block['values'])})"
    if block['kind'] != 'periodic':
        raise ValueError('unknown native block constructor')
    return f"(.periodic {block['repetitions']} ({block['stride']}) {len(block['values'])} {pack(block['values'])})"


def ranges(first, stop, depth):
    if depth == 0:
        return [(first, stop)]
    middle = (first + stop) // 2
    return ranges(first, middle, depth - 1) + ranges(middle, stop, depth - 1)


def tree(leaves):
    if len(leaves) == 1:
        return leaves[0]
    middle = len(leaves) // 2
    return '(' + tree(leaves[:middle]) + ' ++ ' + tree(leaves[middle:]) + ')'


def binding_tree(first, stop):
    if stop - first == 1:
        return f'binding{first}'
    middle = (first + stop) // 2
    return ('(congrArg₂ (fun left right : List Block => left ++ right) ' +
            binding_tree(first, middle) + ' ' + binding_tree(middle, stop) + ')')


def generated(artifact, finalizer):
    blocks = native_blocks(artifact)
    parts = ranges(0, len(blocks), 6)
    data = '''import Airbender.Proofs.Tables.PackedXor9Checks
import Airbender.Proofs.Blake2G.Xor9Partitions
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Blake2G.Proofs.Xor9PackedCapture
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

'''
    for index, (first, stop) in enumerate(parts):
        data += f'def blocks{index} : List Code := [' + ', '.join(map(term, blocks[first:stop])) + ']\n'
    data += '\ndef blocks : List Code := ' + tree([f'blocks{index}' for index in range(64)]) + '\n\n'
    for index in range(64):
        data += f'numeric_data_binding binding{index} : blocks{index}.map (Code.decode 65536) = Xor9Certificate.xor9ColumnBlocks{index}.toList\n'
    data += '\ntheorem source_binding : blocks.map (Code.decode 65536) = (xor9Data.columns[2]).blocks.toList := by\n'
    data += '  change blocks.map (Code.decode 65536) = Xor9Certificate.xor9Column.blocks.toList\n'
    data += '  have joined : Xor9Certificate.xor9Column.blocks = ' + tree([f'Xor9Certificate.xor9ColumnBlocks{i}' for i in range(64)]) + ' := rfl\n'
    data += '  rw [joined]\n  simpa only [blocks, List.map_append, Array.toList_append] using ' + binding_tree(0, 64) + '\n\n'
    data += 'def requests : List PackedXor9Checks.Request := [\n' + ',\n'.join(
        f'  ⟨{sum(map(block_length, blocks[:first]))}, blocks{i}, {sum(map(block_length, blocks[first:stop]))}⟩' for i, (first, stop) in enumerate(parts)) + ']\n\n'
    data += f'end {PREFIX}.Xor9PackedCapture\n'
    certificate = '''import Airbender.Proofs.Blake2G.Xor9PackedCapture

namespace Airbender.Blake2G.Proofs.Xor9PackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedXor9Checks.checkRequests requests = true := by decide +kernel

end Airbender.Blake2G.Proofs.Xor9PackedCapture
'''
    public = '''import Airbender.Proofs.Blake2G.Xor9PackedCertificate

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

'''
    for index in range(64):
        request = f'⟨xor9ColumnStart{index}, Xor9PackedCapture.blocks{index}, xor9ColumnSize{index}⟩'
        proof = (f'PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked\n'
                 f'    {index} ({request}) (by rfl)')
        public += f'''theorem extent{index} :
    (xor9ColumnBlocks{index}.toList.map Block.length).sum = xor9ColumnSize{index} := by
  have result := ({proof}).2
  rw [Xor9PackedCapture.binding{index}] at result
  exact result

theorem output_part{index} :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart{index}
      xor9ColumnBlocks{index}.toList = true := by
  have result := ({proof}).1
  rw [Xor9PackedCapture.binding{index}] at result
  exact result

'''
    public += finalizer + f'\nend {PREFIX}.Xor9Certificate\n'
    return {f'{BASE}/Xor9PackedCapture.lean': data,
            f'{BASE}/Xor9PackedCertificate.lean': certificate,
            f'{BASE}/Xor9Certificate.lean': public}


def retired():
    return [f'{BASE}/Xor9CertificatePart{index}.lean' for index in range(64)] + [f'{BASE}/Xor9Extents.lean']


def write_or_check(root, files, write):
    for relative, content in files.items():
        path = root / relative
        if not path.exists() or path.read_text() != content:
            if not write:
                raise ValueError('packed XOR9 output changed: ' + relative)
            path.write_text(content)
    for relative in retired():
        path = root / relative
        if not path.exists():
            continue
        tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', str(path)], cwd=root,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
        if tracked:
            if not write:
                raise ValueError('retired XOR9 proof shard remains: ' + relative)
            path.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = json.loads((ROOT / 'artifacts/setup/blake-g.json').read_text())
    finalizer = (ROOT / 'scripts/templates/xor9_output_checks.lean').read_text()
    write_or_check(ROOT, generated(artifact, finalizer), args.write)
    print('PASS packed XOR9 capture; all 64 output and size corollaries remain')


if __name__ == '__main__':
    main()
