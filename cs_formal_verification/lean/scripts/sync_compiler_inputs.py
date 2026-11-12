#!/usr/bin/env python3
"""Track each compiler JSON at its direct reader modules."""
from pathlib import Path
import argparse
import json
import re
import tomllib

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
path = ROOT / 'lakefile.toml'
source = path.read_text()
config = tomllib.loads(source)
inputs = {entry['path']: entry['name'] for entry in config.get('input_file', [])}
certificates = json.loads((ROOT / 'compiler_certificate_pins.json').read_text())
for certificate in certificates:
    if certificate in inputs:
        continue
    name = 'compiler_certificate_' + re.sub(r'[^a-zA-Z0-9]+', '_', certificate.removeprefix('artifacts/compiler/').removesuffix('.json'))
    source += f'\n[[input_file]]\nname = "{name}"\npath = "{certificate}"\ntext = true\n'
    inputs[certificate] = name
libraries = {root: library for library in config['lean_lib'] for root in library.get('roots', [])}
readers = 0
for directory in ('GKRCompiler', 'GKRProtocol', 'Import/GKRCompiler', 'Import/GKRProtocol'):
    for reader in sorted((ROOT / 'proven/Proven' / directory).rglob('*.lean')):
        files = sorted(set(re.findall(r'"(artifacts/compiler/[^"\n]+\.json)"', reader.read_text())))
        if not files:
            continue
        module = '.'.join(reader.relative_to(ROOT / 'proven').with_suffix('').parts)
        needs = [inputs[file] for file in files]
        if module in libraries:
            if not set(needs) <= set(libraries[module].get('needs', [])):
                raise ValueError('Update the existing reader needs: ' + module)
            continue
        name = 'CompilerInputs_' + module.removeprefix('Proven.').replace('.', '_')
        source += '\n# A compiler JSON change rebuilds its direct reader and importers.\n'
        source += f'[[lean_lib]]\nname = "{name}"\nsrcDir = "proven"\nroots = ["{module}"]\nneeds = ' + json.dumps(needs) + '\n'
        readers += 1
if args.check:
    if source != path.read_text():
        raise SystemExit('Compiler reader inputs are stale: run scripts/sync_compiler_inputs.py')
    print('PASS compiler readers track their JSON inputs')
else:
    path.write_text(source)
    print(f'Added {readers} compiler reader libraries')
