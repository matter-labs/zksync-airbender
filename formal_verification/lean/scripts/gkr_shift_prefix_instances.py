#!/usr/bin/env python3
"""Generate complete Shift prefix checks and their imported data bindings."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN

PREFIX = 524545
CHUNK = 128
PER_MODULE = 8
REGIONS = ['byteZeroData', 'byteSignData', 'byteXorData', 'byteOrData', 'byteAndData', 'byteTruncateData']


def block_length(block):
    return block.get('length', len(block.get('values', [])) * block.get('repetitions', 1))


def plans(artifact, column, prefix=PREFIX, chunk_size=CHUNK):
    blocks = artifact['columns'][column]['blocks']
    source = [0]
    for block in blocks:
        source.append(source[-1] + block_length(block))
    if prefix not in source:
        raise ValueError('fixed Shift prefix cuts a source block')
    stop = source.index(prefix)
    targets = []
    for kind, region in enumerate(artifact['tables']):
        start, end = region['offset'], region['offset'] + region['length']
        cursor, pieces = start, []
        for index, block in enumerate(blocks):
            lo, hi = max(start, source[index]), min(end, source[index + 1])
            if lo >= hi:
                continue
            count, offset = hi - lo, lo - source[index]
            if offset == 0 and count == block_length(block) or block['kind'] in ['affine', 'dense']:
                lengths = [count]
            else:
                period = len(block['values'])
                leading = min(count, (period - offset % period) % period)
                lengths = [leading, (count - leading) // period * period, (count - leading) % period]
            for length in lengths:
                if length:
                    pieces.append((cursor, cursor + length))
                    cursor += length
        if cursor != end:
            raise ValueError('Shift region coverage changed')
        targets.append((kind, pieces))
    result = []
    for first in range(0, stop, chunk_size):
        last = min(first + chunk_size, stop)
        lo, hi = source[first], source[last]
        selected = []
        for kind, pieces in targets:
            indices = [i for i, (a, b) in enumerate(pieces) if a >= lo and b <= hi]
            if indices:
                if indices != list(range(min(indices), max(indices) + 1)):
                    raise ValueError('nonconsecutive target block span')
                selected.append((kind, min(indices), max(indices) + 1))
        selected_length = sum(targets[k][1][b - 1][1] - targets[k][1][a][0] for k, a, b in selected)
        if selected_length != hi - lo:
            raise ValueError('source and target block boundaries differ')
        result.append((first, last, lo, hi, selected))
    return stop, result


def modules(artifact, column):
    stop, chunks = plans(artifact, column)
    namespace = 'Airbender.Compiler.ShiftPrefixNative.Column' + str(column)
    targets = []
    for begin in range(0, len(chunks), PER_MODULE):
        part = begin // PER_MODULE
        target = 'Airbender.Proofs.GKRProtocol.ShiftPrefixParts.Column' + str(column) + '.Part' + str(part)
        targets.append(target)
        text = ('import Airbender.Import.GKRProtocol.BlockPartsImport\nimport Airbender.Data.GKRSetup.ShiftBinop\n'
                'import Airbender.Data.Tables.ShiftData\n\n' +
                f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
                'set_option warningAsError true\nset_option Elab.async false\n'
                'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
        for index in range(begin, min(begin + PER_MODULE, len(chunks))):
            first, last, lo, hi, selected = chunks[index]
            text += (f'column_blocks_part original{index} from Data.GKRSetup.ShiftBinop.setupColumn{column}\n'
                     f'  start {first} stop {last}\n')
            names = []
            for kind, start, end in selected:
                name = f'target{index}Region{kind}'
                term = (f'(Verification.{REGIONS[kind]}.columns[({column} : Nat)])' if kind < 6
                        else f'Verification.byteShiftColumn{column}')
                text += f'column_blocks_part {name} from {term} start {start} stop {end}\n'
                names.append(name)
            proof = (f'exact congrArg normalizeSetupBlocks (show original{index} = target{index} from rfl)'
                     if sum(end - start for _, start, end in selected) == last - first else 'rfl')
            text += (f'noncomputable def target{index} : List Setup.Block := ' + ' ++ '.join(names) + '\n\n'
                     f'theorem chunkChecked{index} : normalizeSetupBlocks original{index} = normalizeSetupBlocks target{index} := by\n  {proof}\n\n'
                     f'theorem chunkLength{index} : (original{index}.map Setup.Block.length).sum = {hi-lo} := by decide +kernel\n\n')
        text += f'end {namespace}\n'
        yield target, text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column', type=int, choices=range(10), action='append')
    parser.add_argument('--part', type=int, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    from gkr_packed_shift_prefix import ADOPTED, capture
    artifact = json.loads((LEAN / 'artifacts/setup/shift-binop.json').read_text())
    for column in args.column or range(10):
        generated = list(capture(artifact, column) if column in ADOPTED else modules(artifact, column))
        obsolete = sorted((LEAN / f'Airbender/Proofs/GKRProtocol/ShiftPrefixParts/Column{column}').glob('Part*.lean')) if column in ADOPTED else []
        if obsolete and args.check:
            raise ValueError('obsolete Shift fact shards remain')
        if args.write:
            for path in obsolete:
                if subprocess.run(['git', 'ls-files', '--error-unmatch', str(path.relative_to(LEAN))], cwd=LEAN,
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
                    raise ValueError('refuse to delete untracked legacy shard: ' + str(path))
        for target, text in generated:
            if args.part and column in ADOPTED:
                raise ValueError('the complete Shift checker has no proof shard selection')
            if args.part and int(target.rsplit('Part', 1)[1]) not in args.part:
                continue
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('Shift prefix proof span changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(target, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)
        if args.write:
            for path in obsolete:
                path.unlink()


if __name__ == '__main__':
    main()
