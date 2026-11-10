#!/usr/bin/env python3
"""Reject changed source prefixes for the exact original projection equation."""
from check_clean_argument_controls import compile_source


def main():
    prefix = '''import Airbender.Proofs.GKRProtocol.HelperProjectionChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler
namespace HelperProjectionControl
def entries : List GKRAddress := [.BaseLayerWitness 3, .BaseLayerMemory 7, .Cached 1 9]
theorem complete_prefix :
    (List.range 2).map (fun index => (entries[index]?).getD (.BaseLayerWitness 0)) = entries.take 2 :=
  HelperProjectionChecks.map_getD_prefix entries (.BaseLayerWitness 0) 2 (by decide +kernel)
'''
    expected = 'entries.take 2 = [GKRAddress.BaseLayerWitness 3, GKRAddress.BaseLayerMemory 7]'
    changes = [('address class', expected.replace('BaseLayerMemory 7', 'BaseLayerWitness 7')),
               ('source coordinate', expected.replace('BaseLayerMemory 7', 'BaseLayerMemory 8')),
               ('complete prefix', expected.replace(', GKRAddress.BaseLayerMemory 7', ''))]
    for label, bad in changes:
        for mutated, statement in [(False, expected), (True, bad)]:
            result = compile_source(prefix + 'numeric_data_binding binding : ' + statement + '\nend HelperProjectionControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1500:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1500:])
        print('PASS helper projection:', label, flush=True)
    print('PASS three exact/kernel mutation pairs', flush=True)


if __name__ == '__main__':
    main()
