#!/usr/bin/env python3
"""Scaffold actual extension-graph checks; build modules strictly sequentially.

The Lean importer reads all equations from retained native artifacts. This
script supplies module boundaries and counts, never replacement equations.
"""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES

BASE = {'LinearBaseFieldRelation', 'MaxQuadratic', 'EnforceSingleMaxQuadraticConstraint',
        'CopyInBaseField', 'MaterializeSingleLookupInput'}

PRODUCT = {'InitialGrandProductFromCaches', 'InitialGrandProductWithoutCaches',
           'MaterializeGrandProductTermExpression', 'CopyInExtensionField', 'TrivialProduct',
           'MaskIntoIdentityProduct', 'InitsOrTeardownsInitialPair'}


def selectors(circuit):
    """Only proof-assembly indices; all equations remain native Lean definitions."""
    caches = [entry for layer in circuit['layers'] for entry in layer['cached_relations']]
    gates = [next(iter(gate['enforced_relation'].items())) for layer in circuit['layers']
             for gate in layer['gates'] + layer['gates_with_external_connections']]
    key = lambda address: json.dumps(address, sort_keys=True)
    definitions = [output for output, _ in caches]
    definitions += [data['output'] for kind, data in gates if kind in {
        'CopyInBaseField', 'CopyInExtensionField', 'MaterializeSingleLookupInput', 'MaterializedVectorLookupInput'}]
    positions = {key(output): index for index, output in enumerate(definitions)}
    base_outputs, ordinal = {}, 0
    for output, relation in caches:
        if 'SingleColumnLookup' in relation:
            base_outputs[key(output)] = ordinal
            ordinal += 1
    for kind, data in gates:
        if kind in BASE:
            if 'output' in data:
                base_outputs[key(data['output'])] = ordinal
            ordinal += 1
    bases = [{'affine': index, 'gate': base_outputs[key(output)]}
             for index, output in enumerate(definitions) if key(output) in base_outputs]
    affine_steps = [None] * len(definitions)
    steps, lookup_steps, product_steps = 0, [], []
    for index, (_, relation) in enumerate(caches):
        if 'SingleColumnLookup' not in relation:
            affine_steps[index] = steps
            steps += 1
    for kind, data in gates:
        step = steps
        lookup = kind.startswith('Lookup') or kind in {'AggregateLookupRationalPair', 'CopyInExtensionField'}
        product = kind in PRODUCT
        if lookup:
            lookup_steps.append(step)
            steps += 1
        if product:
            product_steps.append(step)
            if not lookup:
                steps += 1
        if kind == 'CopyInExtensionField':
            affine_steps[positions[key(data['output'])]] = step
        elif kind == 'MaterializedVectorLookupInput':
            affine_steps[positions[key(data['output'])]] = step
            steps += 1
    return {'steps': steps, 'affine_steps': affine_steps, 'base': bases,
            'lookup_steps': lookup_steps, 'product_steps': product_steps}


def modules(name, case, pair):
    circuit = pair['circuit']
    caches = [cache for layer in circuit['layers'] for _, cache in layer['cached_relations']]
    gates = [next(iter(gate['enforced_relation'])) for layer in circuit['layers']
             for gate in layer['gates'] + layer['gates_with_external_connections']]
    steps = sum('SingleColumnLookup' not in cache for cache in caches) + sum(kind not in BASE for kind in gates)
    bases = sum('SingleColumnLookup' in cache for cache in caches) + sum(
        kind in {'CopyInBaseField', 'MaterializeSingleLookupInput'} for kind in gates)
    prefix = 'Airbender.Proofs.GKRProtocol.FunctionalNative.' + case
    namespace = 'Airbender.Compiler.FunctionalNative.' + case
    arguments = (f'native from "artifacts/compiler/{name}.json"\n'
                 f'  typing Airbender.Compiler.ConsumerNative.{case}.native.typing\n'
                 f'  lookup Airbender.Compiler.LookupNative.{case}.native\n'
                 f'  product Airbender.Compiler.ProductNative.{case}.native\n'
                 f'  base Airbender.Compiler.FullArithmeticNative.{case}.native')

    def wrap(imports, command):
        return (''.join('import ' + item + '\n' for item in imports) + '\n'
                f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
                'set_option warningAsError true\nset_option Elab.async false\n'
                'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
                + command + '\n\n' + f'end {namespace}\n')

    foundation = prefix + 'Foundation'
    result = [(foundation, wrap(['Airbender.Import.GKRProtocol.FunctionalImport',
               'Airbender.Proofs.GKRProtocol.FullArithmeticNative.' + case,
               'Airbender.Proofs.GKRProtocol.LookupNative.' + case, 'Airbender.Proofs.GKRProtocol.ProductNative.' + case],
               'import_functional_graph ' + arguments))]
    parts = []
    for phase, (label, count) in enumerate([('Steps', steps), ('Base', bases)]):
        for part, start in enumerate(range(0, count, 32)):
            module = prefix + label + str(part)
            parts.append(module)
            result.append((module, wrap([foundation],
                f'check_functional_graph native phase {phase} start {start} stop {min(start+32,count)}')))
    assembly = selectors(circuit)
    assert assembly['steps'] == steps and len(assembly['base']) == bases
    assembly_text = json.dumps(json.dumps(assembly, separators=(',', ':')))
    result.append((prefix, wrap([foundation] + parts + ['Airbender.Import.GKRProtocol.FunctionalFinalize'],
        f'finalize_checked_functional_graph native selectors {assembly_text}\n'
        f'  lookup Airbender.Compiler.LookupNative.{case}.native\n'
        f'  product Airbender.Compiler.ProductNative.{case}.native\n'
        f'  base Airbender.Compiler.FullArithmeticNative.{case}.native')))
    return result, steps, bases


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
            targets, steps, bases = modules(name, case, pair)
            for module, content in targets:
                path = LEAN / (module.replace('.', '/') + '.lean')
                if args.check and (not path.exists() or path.read_text() != content):
                    raise ValueError('functional scaffold changed: ' + module)
                if args.write and (not path.exists() or path.read_text() != content):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content)
            print(name, 'functional steps', steps, 'base affine definitions', bases, flush=True)
            if args.build:
                for module, _ in targets:
                    subprocess.run(['lake', '--no-cache', 'build', '+' + module + ':olean'],
                                   cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
