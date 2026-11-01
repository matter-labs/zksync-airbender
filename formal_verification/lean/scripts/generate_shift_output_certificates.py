#!/usr/bin/env python3
"""Derive the original shift output facts from the complete packed checkers."""
import argparse
import json
from pathlib import Path

from generate_shift_packed_encoding import native_blocks
from generate_packed_xor9 import block_length, ranges, tree

ROOT = Path(__file__).resolve().parents[1]


def join(values, operator):
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return '(' + join(values[:middle], operator) + operator + join(values[middle:], operator) + ')'


def projection(index, size=16):
    if size == 1:
        return ''
    half = size // 2
    return ('.1' + projection(index, half)) if index < half else ('.2' + projection(index - half, half))


def generated(artifact, lane):
    blocks = native_blocks(artifact, lane)
    parts = ranges(0, len(blocks), 4)
    starts = [sum(map(block_length, blocks[:first])) for first, _ in parts]
    statements = [f'checkBlocks (outputByte {lane}) {starts[i]} output{lane}Blocks{i}.toList = true'
                  for i in range(16)]
    joined = tree([f'output{lane}Blocks{i}' for i in range(16)])
    extents = ', '.join(f'output{lane}_extent{i}' for i in range(15))
    simplify = ('Array.toList_append, checkBlocks_append_iff,\n'
                '    List.map_append, List.sum_append, Nat.zero_add,\n'
                f'    {extents}, Nat.reduceAdd')
    code = f'''import Airbender.Proofs.Tables.ShiftOutputExtent{lane}
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

private theorem all_parts :
    {join(statements, ' ∧ ')} := by
  have result := ShiftPackedEncoding.Lane{lane}.native_checks
  have joined : byteShiftColumn{lane+4}.blocks = {joined} := rfl
  rw [joined] at result
  simp only [{simplify}] at result
  exact result

'''
    for index, statement in enumerate(statements):
        code += f'theorem output{lane}_part{index} :\n    {statement} := all_parts{projection(index)}\n\n'
    names = [f'output{lane}_part{i}' for i in range(16)]
    pairs = join(names, ', ').replace('(', '⟨').replace(')', '⟩')
    code += f'''theorem output{lane}_checks :
    checkBlocks (outputByte {lane}) 0 byteShiftColumn{lane+4}.blocks.toList = true := by
  have joined : byteShiftColumn{lane+4}.blocks = {joined} := rfl
  rw [joined]
  simp only [{simplify}]
  exact {pairs}

end Airbender.Verification.ShiftCertificate
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    artifact = json.loads((ROOT / 'artifacts/setup/shift-binop.json').read_text())
    for lane in range(4):
        relative = f'Airbender/Proofs/Tables/ShiftOutputCertificate{lane}.lean'
        path = ROOT / relative
        content = generated(artifact, lane)
        if not path.exists() or path.read_text() != content:
            if not args.write:
                raise ValueError('shift public corollaries changed: ' + relative)
            path.write_text(content)
        for part in range(16):
            old = ROOT / f'Airbender/Proofs/Tables/ShiftOutputCertificate{lane}Part{part}.lean'
            if old.exists():
                if not args.write:
                    raise ValueError('old shift proof shard remains: ' + str(old))
                old.unlink()
    print('PASS all 64 original shift facts and four finalizers')


if __name__ == '__main__':
    main()
