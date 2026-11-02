#!/usr/bin/env python3
"""Reject changed helper candidates, omitted source windows and invalid phases."""
import argparse
from check_clean_argument_controls import compile_source
from gkr_packed_helper_payload import CASES, capture_name, selectors, native
import gkr_helper_instances as legacy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks
import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.AddSubCached.Inputs
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericFunctionalBaseChecks
namespace NativePayloadControl
set_option maxRecDepth 8192
private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩
def relations (n : Nat) : List (Polynomial n Source.BaseField) := [[(1, [])]]
def zeroRecipe : NativeBaseRecipe := .constant 0
def candidate (n : Nat) : HelperAgreement (relations n) zeroRecipe :=
  ⟨.memory (.constant 1), [([(1, [])], ⟨0, by simp [relations]⟩)]⟩
def missingWitness (n : Nat) : HelperAgreement (relations n) zeroRecipe :=
  {candidate n with witness := []}
def badCoefficient (n : Nat) : HelperAgreement (relations n) zeroRecipe :=
  {candidate n with witness := [([(2, [])], ⟨0, by simp [relations]⟩)]}
'''
    source = ('NumericNativePayloadChecks.ofHelper (candidate _) HelperNative.AddSubCached.native.placement '
              'MemoryNative.AddSubCached.native.bank ConsumerNative.AddSubCached.native.typing')
    exact = 'check babyBearModulus [encode (' + source + ')] = true'
    changes = [] if args.case else [
        ('nonempty witness', exact, exact.replace('(candidate _)', '(missingWitness _)'), ''),
        ('witness coefficient', exact, exact.replace('(candidate _)', '(badCoefficient _)'), ''),
        ('zero term fidelity', '(encode (' + source + ')).right = [(0, []), (1, [])]',
         '(encode (' + source + ')).right = [(1, [])]', ''),
    ]
    for case in args.case or CASES:
        owner = 'Airbender.Compiler.HelperPayloadChecks.' + case
        ids = [row['native_leaf'] for row in selectors(case)['operands']]
        imports = 'import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.' + case + '.Data\n'
        for index in sorted({0, len(ids) - 1}):
            chunk, offset = index // 4 * 4, index % 4
            view = f'({owner}.data.drop {index}).take 1'
            piece = f'({owner}.data{chunk}.drop {offset}).take 1'
            from gkr_packed_helper_payload import source as original_source
            typed = '[encode (' + original_source(case, ids[index]) + ')]'
            changes.append((case + ' view ' + str(index), view + ' = ' + piece,
                            '(' + view + ').drop 1 = ' + piece, imports))
            changes.append((case + ' source ' + str(index), piece + ' = ' + typed,
                            '(' + piece + ').drop 1 = ' + typed, imports))
    for label, good, bad, imports in changes:
        for mutated, statement in [(False, good), (True, bad)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement
                                    + '\nend NativePayloadControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1800:])
        print('PASS helper payload:', label, flush=True)
    if not args.case:
        result = compile_source(legacy.module(capture_name('AddSubCached'), 'AddSubCached')[1]
                                .replace('Airbender.Compiler.HelperNative.AddSubCached', 'HelperPayloadLegacy'))
        if result.returncode:
            raise SystemExit('Legacy helper importer:\n' + result.stdout[-1800:])
        print('PASS original helper importer', flush=True)
        text = native('AddSubCached')[1].replace('Airbender.Compiler.HelperNative.AddSubCached', 'HelperPayloadBadPhase')
        for suffix in ['phase 0 using_checks MissingFacts', 'phase 1', 'phase 3']:
            broken = text.replace('phase 1 using_checks Airbender.Compiler.HelperPayloadChecks.AddSubCached', suffix)
            result = compile_source(broken)
            if not result.returncode or not any(message in result.stdout for message in ['helper phase 1 requires', 'helper phase must']):
                raise SystemExit('Invalid helper phase:\n' + result.stdout[-1800:])
        print('PASS helper phase controls', flush=True)
        result = compile_source('''import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport
open Airbender.Compiler
opaque hidden : List NumericFunctionalBaseChecks.Data := []
numeric_functional_base_capture data := hidden
''')
        if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
            raise SystemExit('Opaque helper payload:\n' + result.stdout[-1800:])
        print('PASS strict importer rejects opaque payload', flush=True)
        wrong = native('AddSubCached')[1].replace('Airbender.Compiler.HelperNative.AddSubCached', 'HelperPayloadBadFacts')
        wrong = wrong.replace('using_checks Airbender.Compiler.HelperPayloadChecks.AddSubCached', 'using_checks HelperPayloadWrongFacts')
        ids = [row['native_leaf'] for row in selectors('AddSubCached')['operands']]
        wrong = wrong.replace('namespace HelperPayloadBadFacts', 'namespace HelperPayloadWrongFacts\n'
            + ''.join(f'theorem operand{leaf} : True := True.intro\n' for leaf in ids)
            + 'end HelperPayloadWrongFacts\nnamespace HelperPayloadBadFacts')
        # Supply original data under the new namespace before the finalizer.
        data = legacy.module(capture_name('AddSubCached'), 'AddSubCached')[1].replace(
            'Airbender.Compiler.HelperNative.AddSubCached', 'HelperPayloadBadFacts')
        data = data.replace('\n\nend HelperPayloadBadFacts', ' phase 0\n\nend HelperPayloadBadFacts')
        result = compile_source(data + '\n' + wrong[wrong.index('namespace HelperPayloadWrongFacts'):])
        if not result.returncode or not any(mark in result.stdout.lower() for mark in ['invalid projection', 'invalid field', 'type mismatch']):
            raise SystemExit('Wrong helper facts:\n' + result.stdout[-1800:])
        print('PASS helper finalizer rejects facts of the wrong type', flush=True)
    print('PASS', len(changes), 'exact/kernel mutation pairs', flush=True)


if __name__ == '__main__':
    main()
