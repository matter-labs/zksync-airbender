#!/usr/bin/env python3
"""Export untrusted literal ports. Exact kernel bindings remain required."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

from export_gkr_translations import LEAN
from gkr_functional_instances import selectors
from gkr_packed_functional_steps import capture_name, digest, source_paths
from gkr_wiring_instances import CASES

CAPTURES = tuple(stem + mode for stem in CASES for mode in ['Cached'])


def materializer(case, count):
    native = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    lines = [f'import Airbender.Proofs.GKRProtocol.FunctionalNative.{case}Foundation',
             'import Airbender.Import.GKRProtocol.NumericFunctionalStepImport',
             f'namespace FunctionalPortExport.{case}', 'open Airbender.Compiler',
             'set_option warningAsError true', 'set_option Elab.async false',
             'set_option maxRecDepth 8192', '']
    for first in range(0, count, 32):
        rows = ',\n  '.join(f'⟨[], {native}.step{index}.outputs.map (NumericFunctionalStepChecks.port {native}.isBase), '
                           f'{native}.step{index}.inputs.map (NumericFunctionalStepChecks.port {native}.isBase)⟩'
                           for index in range(first, min(first + 32, count)))
        lines.append('set_option maxHeartbeats 2000000 in\n'
                     f'numeric_functional_steps_capture ports{first} := [\n  {rows}]\n')
    return '\n'.join(lines) + '\nend FunctionalPortExport.' + case + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CAPTURES, action='append', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    for case in args.case:
        name = capture_name(case)
        count = selectors(json.loads((LEAN / f'artifacts/compiler/{name}.json').read_text())['circuit'])['steps']
        with tempfile.TemporaryDirectory(prefix='airbender-functional-ports-') as directory:
            root = Path(directory)
            path = root / 'FunctionalPortCapture.lean'
            path.write_text(materializer(case, count))
            subprocess.run(['lean', '--root=' + str(root), '--tstack=2097152', '-j1', '-o',
                            str(path.with_suffix('.olean')), str(path)], cwd=LEAN, env=environment, check=True)
            exported = root / 'ports.json'
            subprocess.run(['lean', '--tstack=32768', '--run', 'scripts/ExportFunctionalPorts.lean',
                            'FunctionalPortCapture', 'FunctionalPortExport.' + case, str(count), str(exported)],
                           cwd=LEAN, env=dict(environment, LEAN_PATH=str(root) + ':' + environment.get('LEAN_PATH', '')),
                           check=True)
            payload = {'format': 1, 'sources': {path: digest(path) for path in source_paths(case)},
                       'ports': json.loads(exported.read_text())}
        target = args.output_dir / (name + '.json')
        if target.exists() and target.read_text() != json.dumps(payload, separators=(',', ':')) + '\n':
            raise ValueError('refuse to replace an existing different port export: ' + str(target))
        target.write_text(json.dumps(payload, separators=(',', ':')) + '\n')
        print('Exported untrusted ports:', target, flush=True)


if __name__ == '__main__':
    main()
