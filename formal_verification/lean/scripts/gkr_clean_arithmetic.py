#!/usr/bin/env python3
"""Untrusted ideal witnesses for the retained post-compiler Clean assertions."""
import argparse
import json
import os
import subprocess

from gkr_full_arithmetic_certificate import synthesize as full_arithmetic
from gkr_arithmetic_certificate import atom, const, plus, times, expression, coefficient, key, packed
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def synthesize(pair, snapshot):
    complete = full_arithmetic(pair, snapshot)
    addresses = complete['addresses']
    coordinates = {json.dumps(address, sort_keys=True): index for index, address in enumerate(addresses)}

    def address(value):
        return coordinates[json.dumps(value, sort_keys=True)]

    def sparse(data):
        polynomial = const(coefficient(data['constant']))
        for scalar, wire in data['linear_terms']:
            polynomial = plus(polynomial, atom(address(wire)), coefficient(scalar))
        for first, terms in data.get('quadratic_terms', []):
            for scalar, second in terms:
                polynomial = plus(polynomial, times(atom(address(first)), atom(address(second))), coefficient(scalar))
        return polynomial

    gates = []
    for layer in pair['circuit']['layers']:
        for output, relation in layer['cached_relations']:
            if 'SingleColumnLookup' in relation:
                gates.append((address(output), sparse(relation['SingleColumnLookup']['relation']['input'])))
    for layer in pair['circuit']['layers']:
        for gate in layer['gates'] + layer['gates_with_external_connections']:
            kind, data = next(iter(gate['enforced_relation'].items()))
            if kind == 'CopyInBaseField':
                gates.append((address(data['output']), atom(address(data['input']))))
            elif kind == 'MaterializeSingleLookupInput':
                gates.append((address(data['output']), sparse(data['input']['input'])))
            elif kind in ['LinearBaseFieldRelation', 'MaxQuadratic', 'EnforceSingleMaxQuadraticConstraint']:
                output = None if kind == 'EnforceSingleMaxQuadraticConstraint' else address(data['output'])
                gates.append((output, sparse(data['input'])))
    if len(gates) != complete['counts']['relations']:
        raise ValueError('post-arithmetic gate inventory differs from the complete native relation')
    lowered = [polynomial if output is None else plus(atom(output), polynomial, -1)
               for output, polynomial in gates]
    definitions = {output: index for index, (output, _) in enumerate(gates)
                   if output is not None and output >= len(complete['inputs'])}

    def reduce_definitions(polynomial):
        polynomial, witness = dict(polynomial), {}
        for _ in range(100000):
            choice = next(((monomial, scalar, wire) for monomial, scalar in polynomial.items()
                           for wire in monomial if wire in definitions), None)
            if choice is None:
                return polynomial, witness
            monomial, scalar, wire = choice
            ordinal = definitions[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): scalar}
            polynomial = plus(polynomial, times(factor, lowered[ordinal]), -1)
            witness[ordinal] = plus(witness.get(ordinal, {}), factor)
        raise ValueError('cyclic native base-field definitions')

    normalized, reductions = {}, []
    for index, relation in enumerate(lowered):
        reduced, witness = reduce_definitions(relation)
        reductions.append(witness)
        if reduced:
            normalized.setdefault(key(reduced), (index, 1))
            normalized.setdefault(key(plus({}, reduced, -1)), (index, -1))
    placement = pair['circuit']['placement_data']
    variable = lambda index: address(placement[str(index)])
    witnesses = []
    for ordinal, statement in enumerate(pair['circuit']['structured_statements']):
        kind, data = next(iter(statement.items()))
        polynomial = expression(data['expr'], variable)
        if kind == 'Define':
            polynomial = plus(atom(variable(data['dst'])), polynomial, -1)
        reduced, witness = reduce_definitions(polynomial)
        if reduced:
            if key(reduced) not in normalized:
                raise ValueError(f'post-compiler assertion {ordinal} lacks a native ideal witness')
            matched, sign = normalized[key(reduced)]
            witness[matched] = plus(witness.get(matched, {}), const(sign))
            for index, factor in reductions[matched].items():
                witness[index] = plus(witness.get(index, {}), factor, -sign)
        witnesses.append([[packed(polynomial), index] for index, polynomial in sorted(witness.items()) if polynomial])
    return {'format_version': 1, 'witnesses': witnesses,
            'counts': {'variables': len(addresses), 'gates': len(gates), 'statements': len(witnesses)}}


def module(name, case, result):
    target = 'GKRProtocol.CleanArithmeticNative.' + case
    namespace = 'Airbender.Compiler.CleanArithmeticNative.' + case
    selectors = json.dumps(json.dumps({'format_version': 1, 'witnesses': result['witnesses']},
                                     separators=(',', ':')))
    content = (f'import GKRProtocol.CleanArithmeticImport\nimport GKRProtocol.FullArithmeticNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_clean_arithmetic native from "artifacts/compiler/{name}.json"\n'
        f'  selectors {selectors}\n'
        f'  base_model Airbender.Compiler.FullArithmeticNative.{case}.native variables {result["counts"]["variables"]}\n\n'
        f'end {namespace}\n')
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
            name, case = family + '-' + mode, stem + mode.title()
            root = LEAN / 'artifacts/compiler'
            result = synthesize(json.loads((root / (name + '.json')).read_text()),
                                json.loads((root / (name + '-source.json')).read_text()))
            target, content = module(name, case, result)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('post-compiler Clean arithmetic scaffold changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, result['counts'], flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
