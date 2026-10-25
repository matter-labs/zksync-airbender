#!/usr/bin/env python3
"""Bind actual retained Clean scalar arguments to source/native query fields."""
import argparse
import json
import os
import re
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def module(family, stem, mode):
    name, case = family + '-' + mode, stem + mode.title()
    target = 'GKRProtocol.CleanArgumentsNative.' + case
    helper = (LEAN / 'GKRProtocol/HelperNative' / (case + '.lean')).read_text()
    indices = json.loads(re.search(r'selectors ("(?:[^"\\]|\\.)*")', helper).group(1))
    prefix = 'Airbender.Compiler.'
    content = (f'import GKRProtocol.CleanLookupArgumentsImport\nimport GKRProtocol.CleanHelperArgumentsImport\n'
        f'import GKRProtocol.CleanArithmeticNative.{case}\nimport GKRProtocol.FunctionalLinksNative.{case}\n\n'
        f'namespace Airbender.Compiler.CleanArgumentsNative.{case}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_clean_lookup_arguments native from "artifacts/compiler/{name}.json"\n'
        f'  certificate "artifacts/compiler/lookup/{name}.json"\n')
    for key, model in [('clean_model','CleanArithmeticNative'),('base_model','FullArithmeticNative'),
                       ('lookup_model','LookupNative'),('query_model','LookupSourceNative'),('links_model','FunctionalLinksNative')]:
        content += '  ' + key + ' ' + prefix + model + '.' + case + '.native\n'
    content += f'\nimport_clean_helper_arguments native from "artifacts/compiler/{name}.json"\n  helper_indices {json.dumps(indices)}\n'
    for key, model in [('clean_model','CleanArithmeticNative'),('base_model','FullArithmeticNative'),
                       ('helper_model','HelperNative'),('memory_model','MemoryNative'),('links_model','FunctionalLinksNative')]:
        content += '  ' + key + ' ' + prefix + model + '.' + case + '.native\n'
    content += f'\nend Airbender.Compiler.CleanArgumentsNative.{case}\n'
    return target, content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, content = module(family, stem, mode)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('retained Clean query argument binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(family + '-' + mode, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
