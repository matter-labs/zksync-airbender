#!/usr/bin/env python3
"""Reject address collisions and incomplete native source or target bindings."""
import argparse
from check_clean_argument_controls import compile_source
from gkr_packed_source_freshness import CASES, metadata
from export_gkr_translations import LEAN


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericSourceFreshnessChecks
namespace FreshnessControl
set_option maxRecDepth 8192
'''
    changes = [] if args.case else [
        ('collision', 'check (encodeAddresses [.BaseLayerWitness 0]) (encodeAddresses [.BaseLayerWitness 1]) = true',
         'check (encodeAddresses [.BaseLayerWitness 1]) (encodeAddresses [.BaseLayerWitness 1]) = true', ''),
        ('address class', 'check (encodeAddresses [.Cached 0 4]) (encodeAddresses [.BaseLayerWitness 4]) = true',
         'check (encodeAddresses [.BaseLayerWitness 4]) (encodeAddresses [.BaseLayerWitness 4]) = true', ''),
        ('zero source coordinate', 'encodeAddresses [.BaseLayerWitness 0] = encodeAddresses [.BaseLayerWitness 0]',
         'encodeAddresses [] = encodeAddresses [.BaseLayerWitness 0]', ''),
        ('complete target vector', 'encodeAddresses [.BaseLayerWitness 4, .BaseLayerWitness 5] = encodeAddresses [.BaseLayerWitness 4, .BaseLayerWitness 5]',
         'encodeAddresses [.BaseLayerWitness 5] = encodeAddresses [.BaseLayerWitness 4, .BaseLayerWitness 5]', ''),
    ]
    for case in args.case or CASES:
        count, _ = metadata(case)
        owner = 'Airbender.Compiler.SourceFreshnessChecks.' + case
        imports = 'import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.' + case + '.Data\n'
        for first in [0, (count - 1) // 8 * 8]:
            width = min(8, count - first)
            left = f'({owner}.data.drop {first}).take {width}'
            right = f'(({owner}.originalEntries.drop {first}).take {width}).map NumericFunctionalBaseChecks.encode'
            changes.append((case + ' source ' + str(first), left + ' = ' + right,
                '(' + left + f').drop {width} = ' + right, imports))
        left = owner + '.targetData'
        right = 'encodeAddresses ' + owner + '.targetAddresses'
        changes.append((case + ' targets', left + ' = ' + right, '(' + left + ').drop 1 = ' + right, imports))
    for label, exact, changed, imports in changes:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement + '\nend FreshnessControl\n')
            if not mutated and result.returncode:raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1800:])
        print('PASS source freshness control:', label, flush=True)
    print('PASS', len(changes), 'exact controls; kernel rejects all mutations', flush=True)
    if not args.case:
        source = (LEAN / 'Airbender/Proofs/GKRProtocol/TableNative/BlakeRoundCached.lean').read_text()
        start = source.index('namespace Airbender.Compiler.TableNative.BlakeRoundCached')
        source = source[:start] + '''namespace FreshnessBadFacts
theorem genericFresh : True := True.intro
theorem timestampFresh : True := True.intro
end FreshnessBadFacts
''' + source[start:]
        source = source.replace('Airbender.Compiler.TableNative.BlakeRoundCached', 'FreshnessBadTable')
        source = source.replace('using_freshness Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached',
            'using_freshness FreshnessBadFacts')
        result = compile_source(source)
        if not result.returncode or 'type mismatch' not in result.stdout.lower():
            raise SystemExit('Unchecked freshness fact:\n' + result.stdout[-1800:])
        print('PASS table importer rejects freshness facts of the wrong type', flush=True)


if __name__ == '__main__':main()
