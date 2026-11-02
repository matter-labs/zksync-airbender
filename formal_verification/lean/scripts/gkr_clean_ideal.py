#!/usr/bin/env python3
"""Generate numeric Clean ideal captures. Lean checks every source binding."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.set_int_max_str_digits(1000000)

ROOT = Path(__file__).resolve().parents[1]
PRIME = 2013265921
from export_gkr_translations import FAMILIES
from gkr_wiring_instances import CASES
import gkr_dense_arithmetic as dense

CAPTURES = {case + mode.title(): family + '-' + mode
            for case, family in zip(CASES, FAMILIES, strict=True) for mode in ('cached',)}
TRACE_CASES = {case for case in CAPTURES if case.startswith(('Bigint', 'Keccak'))}
ROW_CASES = {case for case in CAPTURES if case.startswith(('BlakeRound', 'Unified'))}


def constructor(value):
    if not isinstance(value, list) or not value or type(value[0]) is not int:
        raise ValueError('invalid numeric expression')
    kind = value[0]
    if kind in (0, 1) and len(value) == 2 and type(value[1]) is int and value[1] >= 0:
        return kind
    if kind in (2, 3) and len(value) == 3:
        return kind
    raise ValueError('invalid numeric expression constructor')


def expand(value):
    kind = constructor(value)
    if kind == 0:
        return [[value[1], []]]
    if kind == 1:
        return [[1, [value[1]]]]
    if kind == 2:
        return expand(value[1]) + expand(value[2])
    if kind == 3:
        return dense.multiply(expand(value[1]), expand(value[2]))
    raise ValueError('unknown numeric expression constructor')


def prepare(case, raw):
    payload = dict(raw)
    if case in TRACE_CASES | ROW_CASES:
        left = [expand(value) for value in payload['expressions']]
        right = [dense.combination(payload['relations'], terms) for terms in payload['witnesses']]
        expected = [dense.normalize(row) for row in left]
        if expected != [dense.normalize(row) for row in right]:
            raise ValueError('Clean ideal equality fails: ' + case)
        payload['expanded'] = left
        payload['combinations'] = right
    if case in TRACE_CASES:
        payload['normalized'] = expected
        payload['normalizationTraces'] = [dense.trace_row(normal, row)
            for rows in [left, right] for normal, row in zip(expected, rows, strict=True)]
    return payload


def selectors(case):
    source = (ROOT / f'Airbender/Proofs/GKRProtocol/CleanArithmeticNative/{case}.lean').read_text()
    return json.loads(json.loads(re.search(r'\bselectors\s+("(?:[^"\\]|\\.)*")', source)[1]))


def provenance(case, name):
    paths = [f'artifacts/compiler/{name}.json', f'artifacts/compiler/{name}-source.json',
             f'Airbender/Proofs/GKRProtocol/FullArithmeticNative/{case}Foundation.lean',
             'Airbender/Import/GKRProtocol/CleanArithmeticImport.lean',
             'Airbender/Proofs/GKRProtocol/CleanIdealChecks.lean', 'scripts/ExportCleanIdeal.lean']
    if case in TRACE_CASES:
        paths += ['Airbender/Proofs/GKRProtocol/CleanIdealTrace.lean', 'scripts/gkr_dense_arithmetic.py']
    if case in ROW_CASES:
        paths += ['Airbender/Proofs/GKRProtocol/CleanIdealRows.lean']
    result = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths}
    result['selectors'] = hashlib.sha256(json.dumps(selectors(case), separators=(',', ':')).encode()).hexdigest()
    return result


def code(value):
    kind = constructor(value)
    if kind in (0, 1):
        return f'(.{"constant" if kind == 0 else "atom"} {value[1]})'
    if kind not in (2, 3):
        raise ValueError('unknown numeric expression constructor')
    return f'(.{"add" if kind == 2 else "mul"} {code(value[1])} {code(value[2])})'


def naturals(values):
    return '[' + ', '.join(map(str, values)) + ']'


def polynomial(values):
    return '[' + ', '.join(f'({scalar}, {naturals(wires)})' for scalar, wires in values) + ']'


def witness(values):
    return '[' + ', '.join(f'({polynomial(factor)}, {index})' for factor, index in values) + ']'


def table(leaves, sizes):
    if len(leaves) == 1:
        return '(.leaf ' + leaves[0] + ')'
    middle = len(leaves) // 2
    return f'(.branch {sum(sizes[:middle])} {table(leaves[:middle], sizes[:middle])} {table(leaves[middle:], sizes[middle:])})'


def binding_tree(proofs, sizes):
    if len(proofs) == 1:
        return '(congrArg NumericPolynomialChecks.LookupTable.leaf ' + proofs[0] + ')'
    middle = len(proofs) // 2
    return f'(congrArg₂ (NumericPolynomialChecks.LookupTable.branch {sum(sizes[:middle])}) ' + \
        binding_tree(proofs[:middle], sizes[:middle]) + ' ' + binding_tree(proofs[middle:], sizes[middle:]) + ')'


def expansion_bindings(payload):
    result = ''
    count = len(payload['expressions'])
    sizes = [min(16, count - index) for index in range(0, count, 16)] or [0]
    for label, source, target, function in [
            ('expanded', 'codes', 'expanded', 'NumericExpressionChecks.Code.polynomial babyBearModulus'),
            ('combinations', 'witnesses', 'combinations', 'NumericArithmeticChecks.combine babyBearModulus relations')]:
        names = []
        for index in range(len(sizes)):
            name = f'{label}_binding{index}'
            names.append(name)
            result += f'numeric_data_binding {name} : {source}{index}.map ({function}) = {target}{index}\n'
        result += f'theorem {label}_binding : CleanIdealChecks.mapTable ({function}) {source} = {target} :=\n  ' + binding_tree(names, sizes) + '\n\n'
    return result


def modules(case, payload):
    namespace = f'Airbender.Compiler.CleanIdealNative.{case}'
    source = f'''import Airbender.Proofs.GKRProtocol.CleanIdealChecks

namespace {namespace}
open Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

'''
    for field, values, render, element_type in [
            ('codes', payload['expressions'], code, 'NumericExpressionChecks.Code'),
            ('relations', payload['relations'], polynomial, 'Data'),
            ('witnesses', payload['witnesses'], witness, 'List (Data × Nat)'),
            ('inputs', payload['inputs'], naturals, 'List Nat')] + (
                [(field, payload[field], polynomial, 'Data') for field in (['normalized', 'expanded', 'combinations'] if case in TRACE_CASES else ['expanded', 'combinations'])] if case in TRACE_CASES | ROW_CASES else []):
        pieces = [values[index:index + 16] for index in range(0, len(values), 16)]
        if not pieces:
            pieces = [[]]
        for index, piece in enumerate(pieces):
            source += f'def {field}{index} : List ({element_type}) := [' + ', '.join(map(render, piece)) + ']\n'
        source += f'\ndef {field} : LookupTable ({element_type}) := ' + table(
            [f'{field}{index}' for index in range(len(pieces))], list(map(len, pieces))) + '\n\n'
    source += f'def capture : CleanIdealChecks.Capture := ⟨codes, relations, witnesses, inputs, {payload["scopeLimit"]}⟩\n\nend {namespace}\n'
    certificate = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Data

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : CleanIdealChecks.check babyBearModulus capture = true := by decide +kernel

end {namespace}
'''
    result = {f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}Data.lean': source,
              f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}.lean': certificate}
    if case in TRACE_CASES:
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}Traces.lean'] = f'''import Airbender.Import.GKRProtocol.NumericTraceDataImport

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
packed_normalization_rows traceRows from "artifacts/compiler/numeric-clean/{CAPTURES[case]}.json" ["normalizationTraces"]
end {namespace}
'''
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}Bindings.lean'] = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Data
import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Traces
import Airbender.Proofs.GKRProtocol.CleanIdealTrace
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def traceCapture : CleanIdealTrace.Capture := ⟨capture, normalized, expanded, combinations, traceRows⟩
{expansion_bindings(payload)}

theorem sources : CleanIdealTrace.Bindings babyBearModulus traceCapture := ⟨expanded_binding, combinations_binding⟩

end {namespace}
'''
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}TraceBindings.lean'] = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Bindings

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
theorem traceBindings : CleanIdealTrace.bindingCheck babyBearModulus traceCapture = true := by decide +kernel
end {namespace}
'''
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}.lean'] = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}TraceBindings

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem traceChecked : CleanIdealTrace.check babyBearModulus traceCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealTrace.check_sound babyBearModulus traceCapture sources traceBindings traceChecked

end {namespace}
'''
    if case in ROW_CASES:
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}Bindings.lean'] = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Data
import Airbender.Proofs.GKRProtocol.CleanIdealRows
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def rowCapture : CleanIdealRows.Capture := ⟨capture, expanded, combinations⟩
{expansion_bindings(payload)}
theorem sources : CleanIdealRows.Bindings babyBearModulus rowCapture := ⟨expanded_binding, combinations_binding⟩
end {namespace}
'''
        result[f'Airbender/Proofs/GKRProtocol/CleanIdealNative/{case}.lean'] = f'''import Airbender.Proofs.GKRProtocol.CleanIdealNative.{case}Bindings

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem rowsChecked : CleanIdealRows.check babyBearModulus rowCapture = true := by decide +kernel
theorem checked : CleanIdealChecks.check babyBearModulus capture = true :=
  CleanIdealRows.check_sound babyBearModulus rowCapture sources rowsChecked
end {namespace}
'''
    return result


def load(case, name):
    payload = json.loads((ROOT / f'artifacts/compiler/numeric-clean/{name}.json').read_text())
    if payload.get('provenance') != provenance(case, name):
        raise ValueError('Clean numeric provenance changed: ' + case)
    extra = {'normalized', 'expanded', 'combinations', 'normalizationTraces'} if case in TRACE_CASES else set()
    if case in ROW_CASES:
        extra = {'expanded', 'combinations'}
    if set(payload) != {'expressions', 'relations', 'witnesses', 'inputs', 'scopeLimit', 'provenance'} | extra:
        raise ValueError('Clean numeric field set changed: ' + case)
    count = len(selectors(case)['witnesses'])
    if any(len(payload[key]) != count for key in ['expressions', 'witnesses', 'inputs']):
        raise ValueError('incomplete Clean numeric inventory: ' + case)
    if case in TRACE_CASES | ROW_CASES:
        expected = prepare(case, payload)
        if any(payload[key] != expected[key] for key in extra):
            raise ValueError('Clean normalization trace changed: ' + case)
    return payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--from-export', type=Path, help='Import exact data emitted by ExportCleanIdeal.lean')
    parser.add_argument('--capture', choices=CAPTURES, action='append')
    args = parser.parse_args()
    selected = {case: name for case, name in CAPTURES.items()
                if not args.capture or case in args.capture}
    for case, name in selected.items():
        if args.from_export:
            if not args.write:
                parser.error('--from-export requires --write')
            payload = prepare(case, json.loads((args.from_export / f'{name}-clean-ideal.json').read_text()))
            payload['provenance'] = provenance(case, name)
            path = ROOT / f'artifacts/compiler/numeric-clean/{name}.json'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(payload, separators=(',', ':')) + '\n')
        for relative, content in modules(case, load(case, name)).items():
            path = ROOT / relative
            if not path.exists() or path.read_text() != content:
                if not args.write:
                    raise ValueError('numeric Clean capture changed: ' + relative)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
    print('PASS', len(selected), 'complete numeric Clean ideal captures')


if __name__ == '__main__':
    main()
