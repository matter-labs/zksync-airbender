#!/usr/bin/env python3
"""Generate complete wiring certificates with exact native key bindings."""
import argparse
import hashlib
import json
from pathlib import Path

from export_gkr_translations import FAMILIES
from gkr_wiring_instances import CASES

ROOT = Path(__file__).resolve().parents[1]
CAPTURES = {case + mode.title(): family + '-' + mode
            for case, family in zip(CASES, FAMILIES, strict=True) for mode in ['cached']}


def provenance(name):
    paths = [f'artifacts/compiler/{name}.json', 'Airbender/Import/GKRCompiler/WiringImport.lean',
             'Airbender/Proofs/GKRCompiler/WiringChecks.lean',
             'Airbender/Proofs/GKRCompiler/WiringKeySort.lean',
             'Airbender/Proofs/GKRCompiler/WiringCheckProjections.lean', 'scripts/ExportWiringKeys.lean']
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths}


def tree(keys):
    if not keys:
        return 'KeyTree.empty'
    middle = len(keys) // 2
    return f'(KeyTree.node {tree(keys[:middle])} {keys[middle]} {tree(keys[middle + 1:])})'


def load(name):
    payload = json.loads((ROOT / f'artifacts/compiler/numeric-wiring/{name}.json').read_text())
    if set(payload) != {'producers', 'placements', 'provenance'}:
        raise ValueError('wiring key field set changed: ' + name)
    if payload['provenance'] != provenance(name):
        raise ValueError('wiring key provenance changed: ' + name)
    for field in ['producers', 'placements']:
        if not isinstance(payload[field], list) or any(type(key) is not int or key < 0 for key in payload[field]):
            raise ValueError('invalid wiring keys: ' + name)
    return payload


def modules(case, payload):
    namespace = f'Airbender.Compiler.WiringCheckNative.{case}'
    native = f'Airbender.Compiler.WiringNative.{case}.native.graph'
    prefix = f'Airbender/Proofs/GKRCompiler/WiringCheckNative/{case}'
    data = f'''import Airbender.Proofs.GKRCompiler.WiringChecks

namespace {namespace}
open Airbender.Compiler.WiringChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def producers : KeyTree := {tree(sorted(payload['producers']))}
def placements : KeyTree := {tree(sorted(payload['placements']))}
def capture : Capture := ⟨producers, placements⟩
end {namespace}
'''
    bindings = f'''import Airbender.Proofs.GKRCompiler.WiringCheckNative.{case}Data
import Airbender.Proofs.GKRCompiler.WiringData.{case}
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

numeric_data_binding producers_binding : producers.toList =
  WiringChecks.KeySort.sort (({native}).produced.map AddressUniqueChecks.addressCode)
numeric_data_binding placements_binding : placements.toList =
  WiringChecks.KeySort.sort (({native}).placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))
theorem bindings : WiringChecks.Bindings {native} capture := ⟨producers_binding, placements_binding⟩
end {namespace}
'''
    certificate = f'''import Airbender.Proofs.GKRCompiler.WiringCheckNative.{case}Bindings

namespace {namespace}
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : WiringChecks.check {native} capture = true := by decide +kernel
theorem original_checked : ({native}).check = true :=
  WiringChecks.check_sound {native} capture bindings checked
end {namespace}
'''
    return {prefix + 'Data.lean': data, prefix + 'Bindings.lean': bindings, prefix + '.lean': certificate}


def legacy_roots(case, name, payload):
    circuit = json.loads((ROOT / f'artifacts/compiler/{name}.json').read_text())['circuit']
    gate_count = sum(len(layer['gates']) + len(layer['gates_with_external_connections']) for layer in circuit['layers'])
    cache_count = sum(len(layer['cached_relations']) for layer in circuit['layers'])
    prefix = f'Airbender.Compiler.WiringNative.{case}.'
    roots = [prefix + 'native.' + field for field in [
        'graph', 'nonemptyChecked', 'producerTableChecked', 'scratchChecked', 'outputsChecked',
        'uniqueChecked', 'placementChecked', 'gatesChecked', 'cachesChecked', 'checked', 'sound']]
    roots += [prefix + 'wiring_valid']
    for field, count in [('gate', gate_count), ('cache', cache_count),
            ('producerUniqueChecked', len(payload['producers'])), ('placementCaseChecked', len(payload['placements'])),
            ('gateChecked', gate_count), ('cacheChecked', cache_count)]:
        roots += [prefix + 'native.' + field + str(index) for index in range(count)]
    return roots


def native_module(case, name, payload):
    source = f'''import Airbender.Import.GKRCompiler.WiringImport
import Airbender.Proofs.GKRCompiler.WiringCheckNative.{case}

namespace Airbender.Compiler.WiringNative.{case}
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

'''
    source += f'import_compiler_wiring native from "artifacts/compiler/{name}.json" phase "certified" start 0 count 0 using Airbender.Compiler.WiringCheckNative.{case}\n'
    source += f'\ntheorem wiring_valid : native.graph.Valid := native.sound\n\nend Airbender.Compiler.WiringNative.{case}\n'
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--capture', choices=CAPTURES, action='append')
    parser.add_argument('--from-export', type=Path)
    args = parser.parse_args()
    selected = {case: name for case, name in CAPTURES.items() if not args.capture or case in args.capture}
    for case, name in selected.items():
        if args.from_export:
            if not args.write:
                parser.error('--from-export requires --write')
            payload = json.loads((args.from_export / f'{name}-wiring-keys.json').read_text())
            payload['provenance'] = provenance(name)
            path = ROOT / f'artifacts/compiler/numeric-wiring/{name}.json'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(payload, separators=(',', ':')) + '\n')
        for relative, content in modules(case, load(name)).items():
            path = ROOT / relative
            if not path.exists() or path.read_text() != content:
                if not args.write:
                    raise ValueError('complete wiring capture changed: ' + relative)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
    print('PASS', len(selected), 'complete wiring captures')


if __name__ == '__main__':
    main()
