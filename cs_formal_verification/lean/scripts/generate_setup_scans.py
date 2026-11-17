#!/usr/bin/env python3
"""Generate the kernel scans that prove each imported setup column equal to its column formula.

`validate` first rejects a configuration that the scan would read loosely (an unknown column, an empty, reversed or
out-of-domain row range, a cut outside the trace, a `per_row` bound inside a period). For each configured setup,
every column is cut into slices of consecutive blocks of about `SLICE` units of kernel work (one unit per row
checked), or the setup's `slice` units. Each slice is one `decide +kernel` check (`Proven.Setup.Scan.SliceOk`), so
the kernel cache of one check stays small. A non-dense block is a long block when its algebraic periods cover at
least the setup's `long_cost` units more than one period: the kernel checks one period, and `long_ok` proves that
the formula repeats with its period and stride (one `long_ok` proof costs about `long_cost` units), outside every
`per_row` range (rows whose formula reads a table, such as controller rows); the kernel checks the remaining rows of
the block one by one. On the rows of a `bitwise` column, `long_ok` closes the formula by congruence only, so a long
block there has stride 0 and the same digits on all its periods. A block across one of the setup's `cuts` rows (a
region bound of the formula) is cut there into pieces (`Cuts.lean`, `Proven.Setup.Cut`), and the scan checks the
pieces. The slices are packed into modules of about `MODULE` units, or the setup's `module` units. `Columns.lean`
joins the slices of each column in order. `--check` regenerates every file in memory, compares it with the committed
file, and fails on a gap or an overlap between the slices of a column.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'proven/Proven/Setup/Native'
SLICE = 25000
MODULE = 100000
# The blocks between two named suffixes of an imported column (`addColumn` in `Human/Import/SetupEmit.lean`).
SUFFIX = 128

# name: the module directory; data: the imported `SetupData`; columns: the fast column formula of each native column;
# long_cost: the kernel work, in rows, that one `long_ok` proof costs;
# unfold: the definitions that `long_ok` unfolds; per_row: the row ranges (first, end) that the kernel checks row by
# row, in every column, or (first, end, columns) in the listed columns only; bitwise: for each column whose formula
# combines digits `(n - first) / divisor % modulus` with bitwise operations on the rows [first, end),
# (first, end, [(divisor, modulus), ...]). `long_ok` closes such a formula only by congruence, so a long block on
# these rows has stride 0 and each digit is the same on all its periods; module: the units of one module, when
# not `MODULE`; cuts: the rows (region bounds) at which the blocks are cut (`Proven.Setup.Cut`), in every column, or
# (row, columns) in the listed columns only, so that `long_ok` sees one region per piece; regions: the lemmas that
# give the formula of each region, which `long_ok` applies before it unfolds the other definitions; slice: the units
# of one slice, when not `SLICE` (a smaller slice keeps the kernel cache of one check small).
# The namespace of the shift/binary column formulas, which the unified formulas read.
SHIFT = 'Airbender.Verification.ShiftBinopSetupProofs'
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
    dict(name='SubwordMemory', json='subword-memory.json', data='Airbender.Compiler.NativeSetups.subwordMemorySetup',
         namespace='Airbender.Compiler.NativeFixedRows.SubwordMemorySetupProofs',
         columns=[f'column{index}' for index in range(9)],
         regions=['byRegion_place', 'byRegion_clear', 'byRegion_loadHalf', 'byRegion_loadByte', 'byRegion_romHalf',
                  'byRegion_romByte', 'byRegion_decoder', 'byRegion_padding'],
         unfold=['fixedZero', 'store', 'loadLow', 'loadHigh', 'loadValue', 'negative', 'halfKey', 'byteKey',
                 'Airbender.Compiler.NativeSetups.Proofs.bit', 'Airbender.Compiler.NativeSetups.Proofs.word',
                 'Bool.false_and', 'Bool.true_and', 'Nat.zero_div', 'Nat.zero_mod'],
         long_cost=2000, per_row=[],
         cuts=[(bound, (1, 2)) for bound in (1, 131073, 262145, 393217, 655361, 4849665, 13238273, 14286849)]),
    dict(name='Unified', slice=10000, json='unified.json', data='Airbender.Compiler.NativeSetups.unifiedSetup',
         namespace='Airbender.Compiler.NativeFixedRows.UnifiedSetupProofs',
         columns=[f'column{index}' for index in range(10)],
         regions=['byRegionShift', 'byRegion_zeroTest', 'byRegion_jump', 'byRegion_sign', 'byRegion_limbSign',
                  'byRegion_low5', 'byRegion_shift', 'byRegion_rom', 'byRegion_rotate', 'byRegion_conditional',
                  'byRegion_wide', 'byRegion_decoder', 'byRegion_padding'],
         unfold=[f'{SHIFT}.column{index}' for index in range(10)] + [
             f'{SHIFT}.{name}' for name in ('byRegion', 'high', 'low', 'output', 'contribution')] + [
             'rotated', 'rotation', 'packedKey', 'decoder', 'Airbender.Compiler.NativeSetups.Proofs.bit',
             'Airbender.Compiler.NativeSetups.Proofs.word'],
         long_cost=2000, per_row=[(327937, 590076, (4, 5, 6, 7)), (1638657, 1900801, (2, 3, 4, 5))],
         cuts=[1, 131073, 196609, 196865, 262401, 327937, 590081, 1638657, 1900801, 1900929, 2097537, 3146113]),
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


def validate(setup, native):
    """Reject a setup configuration that the scan would read loosely: a formula count that differs from the native
    column count, a column number outside the setup, an empty, reversed or out-of-domain row range, a cut row outside
    the trace, or a `per_row` bound inside a period of a periodic block (the scan would move it to a period bound)."""
    name, width, trace_len = setup['name'], len(native['columns']), native['trace_len']
    if len(setup['columns']) != width:
        raise ValueError(f"{name}: {width} native columns, {len(setup['columns'])} column formulas")

    def check_columns(kind, columns):
        if not columns or any(not isinstance(column, int) or not 0 <= column < width for column in columns):
            raise ValueError(f'{name}: {kind} names a column outside 0..{width - 1}: {columns}')

    def check_range(kind, first, end):
        if not 0 <= first < end <= trace_len:
            raise ValueError(f'{name}: {kind} range [{first}, {end}) is empty, reversed or outside [0, {trace_len}]')

    for item in setup['per_row']:
        if len(item) not in (2, 3):
            raise ValueError(f'{name}: per_row entry {item} is not (first, end) or (first, end, columns)')
        check_range('per_row', item[0], item[1])
        if len(item) == 3:
            check_columns('per_row', item[2])
    for column, (first, end, places) in setup.get('bitwise', {}).items():
        check_columns('bitwise', [column])
        check_range('bitwise', first, end)
        if not places or any(divisor <= 0 or modulus <= 0 for divisor, modulus in places):
            raise ValueError(f'{name}: bitwise column {column} has no digits or a digit of zero width')
    for item in setup.get('cuts', []):
        row = item[0] if isinstance(item, tuple) else item
        if isinstance(item, tuple):
            check_columns('cuts', item[1])
        if not 0 < row < trace_len:
            raise ValueError(f'{name}: cut row {row} is outside (0, {trace_len})')
    for column, data in enumerate(native['columns']):
        bounds = {bound for item in setup['per_row'] if len(item) == 2 or column in item[2] for bound in item[:2]}
        row = 0
        for block in data['blocks']:
            size = block_rows(block)
            if block['kind'] == 'periodic':
                period = len(block['values'])
                for bound in sorted(bounds):
                    if row < bound < row + size and (bound - row) % period:
                        raise ValueError(f'{name} column {column}: per_row bound {bound} is inside a period of the '
                                         f'block at row {row} (period {period})')
            row += size


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
        period = 1 if block['kind'] == 'affine' else len(block['values'])
        if block['kind'] == 'dense' or length <= 0 or length % period or length >= block_rows(block):
            raise ValueError(f'cut length {length} does not split the {block["kind"]} block of '
                             f'{block_rows(block)} rows on a period bound')
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
            if units >= setup.get('slice', SLICE) or index == len(blocks) - 1:
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


def suffix(block):
    """The first block of the named suffix (`addColumn` in `SetupEmit`) that holds `block`."""
    return block // SUFFIX * SUFFIX


def long_term(long):
    start, skip, period, reps, stride = long
    return f'⟨{start}, {skip}, {period}, {reps}, {stride}⟩'


def outputs():
    result = {}
    for setup in SETUPS:
        native = json.loads((ROOT / 'artifacts/setup' / setup['json']).read_bytes())
        validate(setup, native)
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
                source, offset = blocks[column], first
                if not cut[column][1]:
                    source, offset = f'{blocks[column]}_from{suffix(first)}', first - suffix(first)
                lines.append(f'theorem {formula}_slice{first} :\n'
                             f'    AllOk {formula} {longs_text} ∧\n'
                             f"    SliceOk {formula} {source} {offset} {count} {longs_text}"
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
            own = [part for part in parts if part[0] == column]
            if not cut[column][1]:
                data = f"{setup['data']}_col{column}"
                for start in range(0, suffix(own[-1][1]) + 1, SUFFIX):
                    proof = 'rfl' if start == 0 else f'drop_from {formula}_from{start - SUFFIX} rfl'
                    lines.append(f'theorem {formula}_from{start} : {data}.drop {start} = {data}_from{start} :=\n'
                                 f'  {proof}\n')
            for _, first, count, _, _, _, _ in own:
                if cut[column][1]:
                    term = f'prefixOk_next ({term})\n    {formula}_slice{first} rfl'
                else:
                    term = (f'prefixOk_next_from ({term})\n    {formula}_from{suffix(first)} (by decide)'
                            f' {formula}_slice{first} rfl')
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
