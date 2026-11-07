#!/usr/bin/env python3
"""Reject changed history address classes, order and complete coverage."""
from check_clean_argument_controls import compile_source


def main():
    prefix = '''import Airbender.Proofs.GKRProtocol.HelperHistoryProjectionChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler HelperHistoryProjectionChecks
namespace HistoryProjectionControl
def bank : WireBank 2 :=
  ⟨fun wire => if wire.val = 0 then .BaseLayerMemory 3 else .BaseLayerMemory 8,
   fun address => if addressEqual address (.BaseLayerMemory 3) then ⟨0, by decide⟩ else ⟨1, by decide⟩⟩
def pairs : List (GKRAddress × GKRAddress) := [(.BaseLayerMemory 3, .BaseLayerMemory 8)]
theorem complete : projectedPairs bank pairs = pairs :=
  projectedPairs_eq bank pairs (by decide +kernel)
'''
    exact = 'projectedPairs bank pairs = [(GKRAddress.BaseLayerMemory 3, GKRAddress.BaseLayerMemory 8)]'
    changes = [('address class', exact.replace('BaseLayerMemory 8', 'BaseLayerWitness 8')),
               ('limb order', exact.replace('BaseLayerMemory 3, GKRAddress.BaseLayerMemory 8',
                                           'BaseLayerMemory 8, GKRAddress.BaseLayerMemory 3')),
               ('complete pair', 'projectedPairs bank pairs = []')]
    for label, bad in changes:
        for mutated, statement in [(False, exact), (True, bad)]:
            result = compile_source(prefix + 'numeric_data_binding binding : ' + statement + '\nend HistoryProjectionControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1500:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1500:])
        print('PASS history projection:', label, flush=True)
    print('PASS three exact/kernel mutation pairs', flush=True)


if __name__ == '__main__':
    main()
