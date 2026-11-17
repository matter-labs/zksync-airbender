#!/usr/bin/env python3
"""Generate the complete native fixed-row comparison suite."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'test/Tests/NativeFixedRows'
CHUNK = 262144
REGIONS = (
    ('SubwordMemory', 'subword-memory', 13238273, 9,
     'Verification.subwordRow Airbender.Compiler.NativeSetups.fixtureWords'),
    ('Unified', 'unified', 2097537, 10,
     'Airbender.Compiler.NativeFixedRows.unified Airbender.Compiler.NativeSetups.fixtureWords'),
)


def outputs():
    result = {}
    modules = []
    for prefix, family, extent, width, function in REGIONS:
        native = json.loads((ROOT / f'artifacts/setup/{family}.json').read_bytes())
        if (native['circuit']['offset_for_decoder_table'] != extent or
                native['circuit']['generic_lookup_tables_width'] != width):
            raise ValueError(f'Fixed region extent differs from native setup: {family}')
        covered = 0
        for number, start in enumerate(range(0, extent, CHUNK)):
            length = min(CHUNK, extent - start)
            if start != covered or length <= 0:
                raise ValueError(f'Fixed region has a gap: {family}')
            covered += length
            name = f'{prefix}{number:03}'
            module = f'Tests.NativeFixedRows.{name}'
            modules.append(module)
            columns = ', '.join(map(str, range(width)))
            result[name + '.lean'] = f'''module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.{prefix}

@[expose] public section
namespace {module}
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/{family}.json" [{start}, {length}] ([{columns}]) =>
  (fun index => {function} ⟨index.val + {start}, by have bound := index.isLt; omega⟩)

end {module}
'''
        if covered != extent:
            raise ValueError(f'Fixed region is incomplete: {family}')
    result['Bindings.lean'] = 'module\n' + ''.join(f'public import {name}\n' for name in modules)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = outputs()
    if args.check:
        if not (DESTINATION / 'Common.lean').is_file():
            raise ValueError('The fixed-row comparison common module is missing')
        actual = {path.name for path in DESTINATION.glob('*.lean')} - {'Common.lean'}
        if actual != set(expected):
            raise ValueError('Fixed-row comparison module inventory differs from the generator')
        for name, text in expected.items():
            if (DESTINATION / name).read_text() != text:
                raise ValueError(f'Fixed-row comparison differs from the generator: {name}')
        print(f'PASS {len(expected) - 1} fixed-row chunks cover every configured region without gaps')
    else:
        DESTINATION.mkdir(parents=True, exist_ok=True)
        for name, text in expected.items():
            (DESTINATION / name).write_text(text)


if __name__ == '__main__':
    main()
