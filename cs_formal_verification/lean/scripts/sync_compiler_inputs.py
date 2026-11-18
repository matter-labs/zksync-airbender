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
for directory in ('GKRCompiler', 'GKRProtocol', 'Import/GKRCompiler', 'Import/GKRProtocol', 'Compiler/WorkerArithmetic'):
    for reader in sorted((ROOT / 'proven/Proven' / directory).rglob('*.lean')):
        files = sorted(set(re.findall(r'"(artifacts/compiler/[^"\n]+\.json)"', reader.read_text())))
        if not files:
            continue
        module = '.'.join(reader.relative_to(ROOT / 'proven').with_suffix('').parts)
        needs = [inputs[file] for file in files]
        for file in files:
            capture = re.fullmatch(r'artifacts/compiler/([a-z0-9-]+)-cached\.json', file)
            if capture:
                layout_input = 'compiler_' + capture[1].replace('-', '_') + '_cached_layout'
                if layout_input not in inputs.values():
                    raise ValueError('Missing cached layout input: ' + file)
                needs.append(layout_input)
        needs = sorted(set(needs))
        if module in libraries:
            existing = libraries[module].get('needs', [])
            if not set(needs) <= set(existing):
                merged = sorted(set(existing) | set(needs))
                pattern = r'(roots = \["' + re.escape(module) + r'"\]\n)needs = \[[^\n]+\]'
                source, count = re.subn(pattern, lambda match: match[1] + 'needs = ' + json.dumps(merged), source)
                if count != 1:
                    raise ValueError('Cannot update reader inputs: ' + module)
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
