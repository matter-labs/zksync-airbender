#!/usr/bin/env python3
"""Generate the kernel scans that prove each imported setup column equal to its column formula.

For each configured setup, every column is cut into slices of consecutive blocks of about `SLICE` units of kernel
work (one unit per row checked). Each slice is one `decide +kernel` check (`Proven.Setup.Scan.SliceOk`), so the kernel
cache of one check stays small. A non-dense block is a long block when its algebraic periods cover at least the
setup's `long_cost` units more than one period: the kernel checks one period, and `long_ok` proves that the formula
repeats with its period and stride (one `long_ok` proof costs about `long_cost` units), outside every
`per_row` range (rows whose formula reads a table, such as controller rows); the kernel checks the remaining rows of the
block one by one. The slices are packed into modules of about `MODULE` units. `Columns.lean` joins the slices of each
column in order. `--check` regenerates every file in memory, compares it with the committed file, and fails on a gap or
an overlap between the slices of a column.
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
# row, in every column, or (first, end, columns) in the listed columns only.
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
    dict(name='AddSub', json='add-sub.json', data='Airbender.Compiler.NativeSetups.addSubSetup',
         namespace='Airbender.Compiler.NativeFixedRows.AddSubSetupProofs',
         columns=[f'column{index}' for index in range(8)],
         unfold=['byRow'], long_cost=2000, per_row=[]),
)


# The setups without kernel scans, with the reason. Every other file of `artifacts/setup` must be scanned.
UNSCANNED = {
    'decoder-smoke.json': 'a Rust test fixture that no claim reads',
    'blake-round.json': 'imported with grid blocks (import_setup_blocks ... with grids)',
    'inits-and-teardowns.json': 'no generic lookup columns',
    'unified.json': 'the compiled comparison in test/Tests/NativeFixedRows binds its fixed region',
    'subword-memory.json': 'the compiled comparison in test/Tests/NativeFixedRows binds its fixed region',
    'keccak-column-parity.json': 'imported with grid blocks (import_setup_blocks ... with grids)',
    'keccak-theta-rho.json': 'imported with grid blocks (import_setup_blocks ... with grids)',
    'keccak-chi5.json': 'imported with grid blocks (import_setup_blocks ... with grids)',
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


def long_of(block, row, per_row, column, long_cost, constant_longs):
    """The `Long` (start, skip, period, covered periods, stride) of a long block, or None for a block checked row by
    row. The covered periods are the longest run of periods outside every `per_row` range; with `constant_longs`,
    a constant block ignores the `per_row` ranges (`long_constant` splits the formula of one row)."""
    if block['kind'] == 'dense' or block_rows(block) < long_cost:
        return None
    if constant_longs and block['kind'] == 'affine' and block['step'] == 0:
        return (row, 0, 1, block['length'], 0)
    if block['kind'] == 'affine':
        period, total, stride = 1, block['length'], block['step']
    else:
        period, total, stride = len(block['values']), block['repetitions'], block['stride']
    per_row = [(item[0], item[1]) for item in per_row if len(item) == 2 or column in item[2]]
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
    return (row, skip, period, reps, stride)


def cost(block, long, long_cost):
    if not long:
        return block_rows(block)
    return block_rows(block) - long[2] * (long[3] - 1) + long_cost


def slices(setup, native):
    """The slices of every column: (column, first block, block count, longs, first row, last row, units)."""
    result = []
    for column, data in enumerate(native['columns']):
        blocks = data['blocks']
        first, row, start_row, longs, units = 0, 0, 0, [], 0
        for index, block in enumerate(blocks):
            long = long_of(block, row, setup['per_row'], column, setup['long_cost'], setup.get('constant_longs'))
            units += cost(block, long, setup['long_cost'])
            if long:
                longs.append(long)
            row += block_rows(block)
            if units >= SLICE or index == len(blocks) - 1:
                result.append((column, first, index + 1 - first, longs, start_row, row, units))
                first, start_row, longs, units = index + 1, row, [], 0
        if row != native['trace_len']:
            raise ValueError(f"{setup['name']} column {column}: blocks cover {row} rows, not {native['trace_len']}")
    return result


def check_partition(setup, native, parts):
    """Each column is covered by consecutive slices, with no gap and no overlap, in blocks and in rows."""
    for column, data in enumerate(native['columns']):
        own = [part for part in parts if part[0] == column]
        next_block, next_row = 0, 0
        for _, first, count, _, start_row, last_row, _ in own:
            if first != next_block or start_row != next_row:
                raise ValueError(f"{setup['name']} column {column}: gap or overlap at block {first}, row {start_row}")
            next_block, next_row = first + count, last_row
        if next_block != len(data['blocks']) or next_row != native['trace_len']:
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
        parts = slices(setup, native)
        check_partition(setup, native, parts)
        first_values = {}
        for column, data in enumerate(native['columns']):
            row = 0
            for block in data['blocks']:
                if block['kind'] == 'affine':
                    first_values[row, column] = block['first']
                row += block_rows(block)
        modules, current, units = [], [], 0
        for part in parts:
            if current and units + part[6] > MODULE:
                modules.append(current)
                current, units = [], 0
            current.append(part)
            units += part[6]
        modules.append(current)
        package = f"Proven.Setup.Native.{setup['name']}"
        spec = f'{package}.Spec'
        unfold = ', '.join(setup['unfold'])
        names = []
        for number, members in enumerate(modules):
            module = f'Slice{number:03}'
            names.append(module)
            header = f'public import {spec}\n' + ('public import Proven.Setup.ScanConstant\n'
                                                   if setup.get('constant_longs') else '')
            lines = [f'module\n{header}\n@[expose] public section\n',
                     f"namespace {setup['namespace']}",
                     'open Airbender.Import.Setup Airbender.Import.Setup.Scan',
                     '-- `long_ok` tries several closing tactics; most proofs use the first.',
                     'set_option linter.unusedTactic false',
                     'set_option linter.unreachableTactic false',
                     'set_option linter.unusedSimpArgs false\n',
                     '/- Generated by scripts/generate_setup_scans.py: kernel scans of consecutive blocks. -/\n']
            for column, first, count, longs, start_row, last_row, _ in members:
                formula = setup['columns'][column]
                definitions = ', '.join([formula] + setup['unfold'])
                longs_text = '[' + ', '.join(long_term(long) for long in longs) + ']'
                long_names = [f'{formula}_long{long[0]}' for long in longs]
                for name, long in zip(long_names, longs):
                    constant = setup.get('constant_longs') and long[2] == 1 and long[4] == 0
                    tactic = (f'long_constant [{definitions}] {first_values[long[0], column]}' if constant
                              else f'long_ok [{definitions}]')
                    lines.append(f'theorem {name} : Long.Ok {formula} {long_term(long)} := by\n  {tactic}\n')
                all_ok = '⟨' + ''.join(f'{name}, ' for name in long_names) + 'trivial⟩' if longs else 'trivial'
                lines.append(f'theorem {formula}_slice{first} :\n'
                             f'    AllOk {formula} {longs_text} ∧\n'
                             f"    SliceOk {formula} {setup['data']}_col{column} {first} {count} {longs_text}"
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
            lines.append(f'theorem {formula}_rows :\n'
                         f"    ∀ n < {native['trace_len']}, decode {setup['data']}_col{column} n = {formula} n :=\n"
                         f'  ({term}).2\n')
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
