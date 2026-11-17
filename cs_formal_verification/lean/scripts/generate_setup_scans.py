#!/usr/bin/env python3
"""Generate the kernel scans that prove each imported setup column equal to its column formula.

For each configured setup, every column is cut into slices of consecutive blocks of about `SLICE` units of kernel
work (one unit per row checked). Each slice is one `decide +kernel` check (`Proven.Setup.Scan.SliceOk`), so the kernel
cache of one check stays small. A non-dense block is a long block when its algebraic periods cover at least the
setup's `long_cost` units more than one period: the kernel checks one period, and `long_ok` proves that the formula
repeats with its period and stride (one `long_ok` proof costs about `long_cost` units), outside every
`per_row` range (rows whose formula reads a table, such as controller rows); the kernel checks the remaining rows of the
block one by one. On the rows of a `bitwise` column, `long_ok` closes the formula by congruence only, so a long block
there has stride 0 and the same digits on all its periods. A block across one of the setup's `cuts` rows (a region
bound of the formula) is cut there into pieces (`Cuts.lean`, `Proven.Setup.Cut`), and the scan checks the pieces. The
slices are packed into modules of about `MODULE` units, or the setup's `module` units. `Columns.lean` joins the slices
of each column in order. `--check` regenerates every file in memory, compares it with the committed file, and fails on
a gap or an overlap between the slices of a column.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'proven/Proven/Setup/Native'
SLICE = 25000
MODULE = 100000

# name: the module directory; data: the imported `SetupData`; columns: the fast column formula of each native column;
# long_cost: the kernel work, in rows, that one `long_ok` proof costs;
# unfold: the definitions that `long_ok` unfolds; per_row: the row ranges (first, end) that the kernel checks row by
# row, in every column, or (first, end, columns) in the listed columns only; bitwise: for each column whose formula
# combines digits `(n - first) / divisor % modulus` with bitwise operations on the rows [first, end),
# (first, end, [(divisor, modulus), ...]). `long_ok` closes such a formula only by congruence, so a long block on
# these rows has stride 0 and each digit is the same on all its periods; module: the units of one module, when
# not `MODULE`; cuts: the rows (region bounds) at which the blocks are cut (`Proven.Setup.Cut`), in every column, or
# (row, columns) in the listed columns only, so that `long_ok` sees one region per piece; regions: the lemmas that
# give the formula of each region, which `long_ok` applies before it unfolds the other definitions.
# The five nibbles of a 20-bit key.
NIBBLES = [(1, 16), (16, 16), (256, 16), (4096, 16), (65536, 16)]

SETUPS = (
    dict(name='Bigint', json='bigint.json', data='Airbender.Compiler.NativeSetups.bigintSetup',
         namespace='Airbender.Bigint.SetupProofs', columns=['column0', 'column1', 'column2'], unfold=[],
         long_cost=2000, per_row=[]),
    dict(name='BlakeG', json='blake-g.json', data='Airbender.Compiler.NativeSetups.blakeGSetup',
         namespace='Airbender.Blake2G.SetupProofs', columns=[f'column{index}' for index in range(9)],
         unfold=['byRegion'], long_cost=4000, per_row=[(344384, 344896)]),
    dict(name='Keccak', json='keccak.json', data='Airbender.Compiler.NativeSetups.keccakSetup',
         namespace='Airbender.Keccak.SetupProofs', columns=[f'column{index}' for index in range(8)],
         unfold=['byRegion', 'rotationHigh', 'rotationLow', 'bySixteen'], long_cost=15000,
         per_row=[(65537, 69633), (69633, 135169, (2,))]),
    dict(name='ShiftBinop', json='shift-binop.json', data='Airbender.Compiler.NativeSetups.shiftBinopSetup',
         namespace='Airbender.Verification.ShiftBinopSetupProofs',
         columns=[f'column{index}' for index in range(10)],
         unfold=['byRegion', 'high', 'low', 'output', 'contribution'], long_cost=4000,
         per_row=[(262401, 524545, (4, 5, 6, 7))]),
    dict(name='MulDiv', json='mul-div.json', data='Airbender.Compiler.NativeSetups.mulDivSetup',
         namespace='Airbender.Compiler.NativeFixedRows.MulDivSetupProofs',
         columns=[f'column{index}' for index in range(9)], unfold=['byRegion'], long_cost=2000, per_row=[]),
    dict(name='WordMemory', json='word-memory.json', data='Airbender.Compiler.NativeSetups.wordMemorySetup',
         namespace='Airbender.Compiler.NativeFixedRows.WordMemorySetupProofs',
         columns=[f'column{index}' for index in range(9)],
         unfold=['byRegion', 'Airbender.Compiler.NativeSetups.Proofs.word'], long_cost=2000, per_row=[]),
    dict(name='JumpBranch', json='jump-branch.json', data='Airbender.Compiler.NativeSetups.jumpBranchSetup',
         namespace='Airbender.Compiler.NativeFixedRows.JumpBranchSetupProofs',
         columns=[f'column{index}' for index in range(10)],
         unfold=['byRegion', 'Airbender.Compiler.NativeSetups.Proofs.bit', 'conditional', 'decoder'],
         long_cost=4000, per_row=[]),
    dict(name='BlakeRound', json='blake-round.json', data='Airbender.Blake2Round.blake2RoundSetup',
         namespace='Airbender.Blake2Round.SetupProofs', columns=[f'column{index}' for index in range(6)],
         unfold=['byRegion', 'nat_shiftLeft'], long_cost=4000,
         per_row=[(344064, 344065, (3,)), (589824, 589825, (4,))]),
    dict(name='AddSub', json='add-sub.json', data='Airbender.Compiler.NativeSetups.addSubSetup',
         namespace='Airbender.Compiler.NativeFixedRows.AddSubSetupProofs',
         columns=[f'column{index}' for index in range(8)],
         unfold=['byRow'], long_cost=2000, per_row=[]),
    dict(name='KeccakColumnParity', module=200000, json='keccak-column-parity.json',
         data='Airbender.Keccak.Split.ColumnParity.columnParitySetup',
         namespace='Airbender.Keccak.Split.ColumnParity.SetupProofs',
         columns=[f'column{index}' for index in range(8)], unfold=['byRegion'], long_cost=2000,
         per_row=[(65536, 65780), (0, 65536, (2,))], bitwise={5: (65780, 1114356, NIBBLES)}),
    dict(name='KeccakThetaRho', module=300000, json='keccak-theta-rho.json',
         data='Airbender.Keccak.Split.ThetaRho.thetaRhoSetup',
         namespace='Airbender.Keccak.Split.ThetaRho.SetupProofs', columns=[f'column{index}' for index in range(9)],
         unfold=['byRegion'], long_cost=2000, per_row=[(589824, 590066), (65536, 589824, (3, 4))]),
    dict(name='KeccakChi5', module=300000, json='keccak-chi5.json', data='Airbender.Keccak.Split.Chi5.chi5Setup',
         namespace='Airbender.Keccak.Split.Chi5.SetupProofs', columns=[f'column{index}' for index in range(11)],
         unfold=['byRegion', 'chiNibble'], long_cost=2000, per_row=[(1048576, 1048697)],
         bitwise={5 + place: (0, 1048576, [NIBBLES[place], NIBBLES[(place + 1) % 5], NIBBLES[(place + 2) % 5]])
                  for place in range(5)}),
)


# The setups without kernel scans, with the reason. Every other file of `artifacts/setup` must be scanned.
UNSCANNED = {
    'decoder-smoke.json': 'a Rust test fixture that no claim reads',
    'inits-and-teardowns.json': 'no generic lookup columns',
    'unified.json': 'the compiled comparison in test/Tests/NativeFixedRows binds its fixed region',
    'subword-memory.json': 'the compiled comparison in test/Tests/NativeFixedRows binds its fixed region',
}


def check_inventory():
    """Each setup file is scanned or listed in `UNSCANNED`, not both."""
    files = {path.name for path in (ROOT / 'artifacts/setup').glob('*.json')}
    scanned = {setup['json'] for setup in SETUPS}
    if scanned & set(UNSCANNED) or files != scanned | set(UNSCANNED):
        raise SystemExit(f'FAIL setup scan inventory: scanned {sorted(scanned)}, files {sorted(files)}')


def block_rows(block):
    if block['kind'] == 'affine':
        return block['length']
    if block['kind'] == 'dense':
        return len(block['values'])
    return block['repetitions'] * len(block['values'])


def same_digits(digits, anchor, period, reps):
    """The periods from row `anchor` lie in the bitwise rows, and each digit `(n - first) / divisor % modulus` is the
    same at row `anchor + q * period + j` for every `q < reps`: the period is a multiple of `divisor * modulus`, or
    the covered rows have one value of `(n - first) / divisor`."""
    first, end, places = digits
    low, high = anchor, anchor + reps * period
    return first <= low and high <= end and all(
        period % (divisor * modulus) == 0 or (low - first) // divisor == (high - 1 - first) // divisor
        for divisor, modulus in places)


def long_of(setup, block, row, column):
    """The `Long` (start, skip, period, covered periods, stride) of a long block, or None for a block checked row by
    row. The covered periods are the longest run of periods outside every `per_row` range."""
    long_cost = setup['long_cost']
    if block['kind'] == 'dense' or block_rows(block) < long_cost:
        return None
    if block['kind'] == 'affine':
        period, total, stride = 1, block['length'], block['step']
    else:
        period, total, stride = len(block['values']), block['repetitions'], block['stride']
    per_row = [(item[0], item[1]) for item in setup['per_row'] if len(item) == 2 or column in item[2]]
    cuts = {0, total}
    for first, stop in per_row:
        low = max(0, (first - row) // period)
        high = min(total, -(-(stop - row) // period))
        if low < high:
            cuts |= {low, high}
    best = (0, 0)
    points = sorted(cuts)
    for low, high in zip(points, points[1:]):
        inside = any(first < row + high * period and row + low * period < stop for first, stop in per_row)
        if not inside and high - low > best[1] - best[0]:
            best = (low, high)
    skip, reps = best[0], best[1] - best[0]
    if period * (reps - 1) < long_cost:
        return None
    digits = setup.get('bitwise', {}).get(column)
    anchor = row + skip * period
    if digits and anchor < digits[1] and digits[0] < anchor + reps * period and (
            stride != 0 or not same_digits(digits, anchor, period, reps)):
        return None
    return (row, skip, period, reps, stride)


def cost(block, long, long_cost):
    if not long:
        return block_rows(block)
    return block_rows(block) - long[2] * (long[3] - 1) + long_cost


def cut_block(block, offsets):
    """The pieces of a block cut at the given offsets from its first row (`Proven.Setup.Cut.cutMany`)."""
    pieces, done = [], 0
    for offset in offsets:
        length = offset - done
        if block['kind'] == 'affine':
            pieces.append(dict(block, length=length))
            block = dict(block, length=block['length'] - length, first=block['first'] + block['step'] * length)
        else:
            periods = length // len(block['values'])
            pieces.append(dict(block, repetitions=periods))
            block = dict(block, repetitions=block['repetitions'] - periods,
                         values=[value + block['stride'] * periods for value in block['values']])
        done = offset
    return pieces + [block]


def cut_column(setup, column, blocks):
    """The blocks of a column cut at the setup's `cuts` rows that fall strictly inside them (for a periodic block,
    at the period bounds around the row), and the `cutColumn` entries (skipped blocks, piece lengths)."""
    rows = sorted(item[0] if isinstance(item, tuple) else item for item in setup.get('cuts', [])
                  if not isinstance(item, tuple) or column in item[1])
    pieces, entries, row, skipped = [], [], 0, 0
    for block in blocks:
        size = block_rows(block)
        offsets = set()
        if block['kind'] != 'dense':
            period = 1 if block['kind'] == 'affine' else len(block['values'])
            for cut in rows:
                if row < cut < row + size:
                    offset = cut - row
                    offsets |= {offset // period * period, -(-offset // period) * period}
        offsets = sorted(offset for offset in offsets if 0 < offset < size)
        if offsets:
            entries.append((skipped, [later - earlier for earlier, later in zip([0] + offsets, offsets)]))
            pieces += cut_block(block, offsets)
            skipped = 0
        else:
            pieces.append(block)
            skipped += 1
        row += size
    return pieces, entries


def slices(setup, columns, trace_len):
    """The slices of every column: (column, first block, block count, longs, first row, last row, units)."""
    result = []
    for column, blocks in enumerate(columns):
        first, row, start_row, longs, units = 0, 0, 0, [], 0
        for index, block in enumerate(blocks):
            long = long_of(setup, block, row, column)
            units += cost(block, long, setup['long_cost'])
            if long:
                longs.append(long)
            row += block_rows(block)
            if units >= SLICE or index == len(blocks) - 1:
                result.append((column, first, index + 1 - first, longs, start_row, row, units))
                first, start_row, longs, units = index + 1, row, [], 0
        if row != trace_len:
            raise ValueError(f"{setup['name']} column {column}: blocks cover {row} rows, not {trace_len}")
    return result


def check_partition(setup, columns, trace_len, parts):
    """Each column is covered by consecutive slices, with no gap and no overlap, in blocks and in rows."""
    for column, blocks in enumerate(columns):
        own = [part for part in parts if part[0] == column]
        next_block, next_row = 0, 0
        for _, first, count, _, start_row, last_row, _ in own:
            if first != next_block or start_row != next_row:
                raise ValueError(f"{setup['name']} column {column}: gap or overlap at block {first}, row {start_row}")
            next_block, next_row = first + count, last_row
        if next_block != len(blocks) or next_row != trace_len:
            raise ValueError(f"{setup['name']} column {column}: slices end at block {next_block}, row {next_row}")


def long_term(long):
    start, skip, period, reps, stride = long
    return f'⟨{start}, {skip}, {period}, {reps}, {stride}⟩'


def outputs():
    result = {}
    for setup in SETUPS:
        native = json.loads((ROOT / 'artifacts/setup' / setup['json']).read_bytes())
        if len(setup['columns']) != len(native['columns']):
            raise ValueError(f"{setup['name']}: {len(native['columns'])} native columns")
        cut = [cut_column(setup, column, data['blocks']) for column, data in enumerate(native['columns'])]
        columns = [pieces for pieces, _ in cut]
        parts = slices(setup, columns, native['trace_len'])
        check_partition(setup, columns, native['trace_len'], parts)
        modules, current, units = [], [], 0
        for part in parts:
            if current and units + part[6] > setup.get('module', MODULE):
                modules.append(current)
                current, units = [], 0
            current.append(part)
            units += part[6]
        modules.append(current)
        package = f"Proven.Setup.Native.{setup['name']}"
        spec = f'{package}.Spec'
        names = []
        blocks = [f"{setup['data']}_col{column}" for column in range(len(columns))]
        if any(entries for _, entries in cut):
            lines = [f'module\npublic import {spec}\npublic import Proven.Setup.Cut\n\n@[expose] public section\n',
                     f"namespace {setup['namespace']}", 'open Airbender.Import.Setup Airbender.Import.Setup.Scan\n',
                     '/- Generated by scripts/generate_setup_scans.py: the columns cut at the region bounds. -/\n']
            for column, (_, entries) in enumerate(cut):
                if entries:
                    formula = setup['columns'][column]
                    text = ', '.join(f'({skip}, {lengths})' for skip, lengths in entries)
                    lines.append(f'noncomputable def {formula}_blocks : List Block :=\n'
                                 f'  cutColumn [{text}]\n    {blocks[column]}\n')
                    lines.append(f'theorem {formula}_blocks_decode (n : Nat) :\n'
                                 f'    decode {formula}_blocks n = decode {blocks[column]} n :=\n'
                                 f'  decode_cutColumn _ _ n\n')
                    blocks[column] = f'{formula}_blocks'
            lines.append(f"end {setup['namespace']}\n")
            result[f"{setup['name']}/Cuts.lean"] = '\n'.join(lines)
            spec = f'{package}.Cuts'
        for number, members in enumerate(modules):
            module = f'Slice{number:03}'
            names.append(module)
            lines = [f'module\npublic import {spec}\n\n@[expose] public section\n',
                     f"namespace {setup['namespace']}",
                     'open Airbender.Import.Setup Airbender.Import.Setup.Scan',
                     '-- `long_ok` tries several closing tactics; most proofs use the first.',
                     'set_option linter.unusedTactic false',
                     'set_option linter.unreachableTactic false',
                     'set_option linter.unusedSimpArgs false',
                     '-- The kernel checks of the `omega` proofs recurse deeply on the large row numbers.',
                     'set_option maxRecDepth 100000\n',
                     '/- Generated by scripts/generate_setup_scans.py: kernel scans of consecutive blocks. -/\n']
            for column, first, count, longs, start_row, last_row, _ in members:
                formula = setup['columns'][column]
                definitions = ', '.join([formula] + setup['unfold'])
                longs_text = '[' + ', '.join(long_term(long) for long in longs) + ']'
                long_names = [f'{formula}_long{long[0]}' for long in longs]
                regions = (' [' + ', '.join([formula] + setup['regions']) + ']') if 'regions' in setup else ''
                for name, long in zip(long_names, longs):
                    lines.append(f'theorem {name} : Long.Ok {formula} {long_term(long)} := by\n'
                                 f'  long_ok [{definitions}]{regions}\n')
                all_ok = '⟨' + ''.join(f'{name}, ' for name in long_names) + 'trivial⟩' if longs else 'trivial'
                lines.append(f'theorem {formula}_slice{first} :\n'
                             f'    AllOk {formula} {longs_text} ∧\n'
                             f"    SliceOk {formula} {blocks[column]} {first} {count} {longs_text}"
                             f' {start_row} {last_row} :=\n'
                             f'  ⟨{all_ok}, by decide +kernel⟩\n')
            lines.append(f"end {setup['namespace']}\n")
            result[f"{setup['name']}/{module}.lean"] = '\n'.join(lines)
        imports = ''.join(f'public import {package}.{name}\n' for name in names)
        lines = [f'module\n{imports}\n@[expose] public section\n', f"namespace {setup['namespace']}",
                 'open Airbender.Import.Setup Airbender.Import.Setup.Scan\n',
                 '/- Generated by scripts/generate_setup_scans.py: the slices of each column, joined in order. -/\n']
        for column, formula in enumerate(setup['columns']):
            term = f'prefixOk_zero {formula} _'
            for _, first, count, _, _, _, _ in (part for part in parts if part[0] == column):
                term = f'prefixOk_next ({term})\n    {formula}_slice{first} rfl'
            proof = f'({term}).2'
            if cut[column][1]:
                proof = f'fun n bound => ({formula}_blocks_decode n).symm.trans (({term}).2 n bound)'
            lines.append(f'theorem {formula}_rows :\n'
                         f"    ∀ n < {native['trace_len']}, decode {setup['data']}_col{column} n = {formula} n :=\n"
                         f'  {proof}\n')
        lines.append(f"end {setup['namespace']}\n")
        result[f"{setup['name']}/Columns.lean"] = '\n'.join(lines)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    check_inventory()
    expected = outputs()
    generated = {setup['name'] for setup in SETUPS}
    if args.check:
        actual = {str(path.relative_to(DESTINATION)) for path in DESTINATION.glob('*/*.lean')
                  if path.parent.name in generated and path.name != 'Spec.lean'}
        if actual != set(expected):
            raise SystemExit('FAIL setup scan module inventory differs from the generator: '
                             f'{sorted(actual ^ set(expected))}')
        for name, text in expected.items():
            if (DESTINATION / name).read_text() != text:
                raise SystemExit(f'FAIL setup scan differs from the generator: {name}')
        print(f'PASS {len(expected)} setup scan modules cover every column without a gap or an overlap')
    else:
        for name in generated:
            for path in (DESTINATION / name).glob('*.lean'):
                if path.name != 'Spec.lean':
                    path.unlink()
        for name, text in expected.items():
            path = DESTINATION / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
