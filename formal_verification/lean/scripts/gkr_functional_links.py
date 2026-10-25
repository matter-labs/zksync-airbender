#!/usr/bin/env python3
"""Connect whole native graph witnesses to independently checked source outputs."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def module(name, case, pair):
    graph = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    typing = 'Airbender.Compiler.ConsumerNative.' + case + '.native.typing'
    lookup = 'Airbender.Compiler.LookupNative.' + case + '.native'
    source = 'Airbender.Compiler.LookupSourceNative.' + case + '.native'
    memory = 'Airbender.Compiler.MemoryNative.' + case + '.native'
    helper = 'Airbender.Compiler.HelperNative.' + case + '.native'
    imports = ['GKRProtocol.FunctionalLinksImport'] + ['GKRProtocol.' + stem + '.' + case
        for stem in ['FunctionalNative', 'LookupSourceNative', 'MemoryNative', 'HelperNative']]
    text = ''.join('import ' + item + '\n' for item in imports)
    namespace = 'Airbender.Compiler.FunctionalLinksNative.' + case
    text += (f'\nnamespace {namespace}\nopen Airbender Airbender.Compiler\n'
             'set_option warningAsError true\nset_option Elab.async false\n'
             'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
             f'import_functional_links native from "artifacts/compiler/{name}.json"\n'
             f'  graph {graph}\n  base_model {base}\n  typing {typing}\n'
             f'  lookup_fields {lookup}\n  lookup_source {source}\n'
             f'  memory_model {memory}\n  helper_model {helper}\n')
    outputs = pair['circuit']['global_output_map']
    reductions = [('timestamp', helper, 'helper', True)]
    for key, label in [('GenericLookup', 'generic'), ('Lookup16Bits', 'range16')]:
        if key in outputs:
            reductions.append((label, source, 'lookup', True))
    for label in ['memoryRead', 'memoryWrite']:
        reductions.append((label, memory, 'memory', False))
    if 'InitsAndTeardownsProduct' in outputs:
        for label in ['initializationRead', 'initializationWrite']:
            reductions.append((label, memory, 'memory', False))
    for label, owner, kind, rational in reductions:
        gamma_arg = ' gamma' if rational else ''
        native_holds = 'canonical_lookups' if rational else 'canonical_products'
        assignment = '(native.assignment hom challenges gamma baseValue)'
        values = f'({assignment}.value {typing} hom)'
        if rational:
            terms = 'timestampTerms' if label == 'timestamp' else label + 'SourceTerms'
            conclusion = (f'({lookup}.{label}Output).value {values} =\n'
                          f'      ({owner}.{terms} hom challenges gamma {assignment}).sum')
        else:
            group = 'PermutationProduct' if kind == 'memory' and label.startswith('memory') else 'InitsAndTeardownsProduct'
            side = 0 if label.endswith('Read') else 1
            constructor, data = next(iter(outputs[group][side].items()))
            if constructor not in {'InnerLayer', 'Cached'}:
                raise ValueError('unexpected native output address: ' + constructor)
            output = f'(GKRAddress.{constructor} {data["layer"]} {data["offset"]})'
            product = f'({owner}.{label}Terms hom challenges {assignment}).prod'
            if label.startswith('memory'):
                product = (f'maskProduct (hom ({owner}.sourceExecute.value ({owner}.sourceValues baseValue)))\n'
                           f'      {product}')
            conclusion = f'{values} {output} =\n      {product}'
        text += (f'\ntheorem {label}_source_witness {{R : Type}} [CommRing R]\n'
                 '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
                 '    (baseValue : GKRAddress → Source.BaseField)\n'
                 f'    (arithmetic : ∀ gate ∈ {base}.artifact.gates,\n'
                 f'      gate.expressionResidual (baseValue ∘ {base}.bank.address) = 0) :\n    {conclusion} :=\n'
                 f'  {owner}.{label}SourceReduction hom challenges{gamma_arg}\n'
                 '    (native.assignment hom challenges gamma baseValue)\n'
                 f'    (native.{kind}Defined hom challenges gamma baseValue arithmetic)\n'
                 f'    (native.{kind}Copies baseValue arithmetic)\n'
                 f'    (by rw [native.assignment_value]; exact {graph}.{native_holds} hom challenges gamma baseValue)\n')
    return 'GKRProtocol.FunctionalLinksNative.' + case, text + '\nend ' + namespace + '\n'


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
            name, case = family + '-' + mode, stem + mode.title()
            pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
            target, content = module(name, case, pair)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('functional source link changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
