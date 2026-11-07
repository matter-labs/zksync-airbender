#!/usr/bin/env python3
"""Check original lookup witnesses, bank predicates and complete source bindings."""
import argparse

from check_clean_argument_controls import compile_source
from gkr_packed_lookup_source import CASES, command, descriptors


def importer_controls():
    head = '''import Airbender.Import.GKRProtocol.LookupSourceImport
import Airbender.Proofs.GKRProtocol.Native.AddSubCached
import Airbender.Proofs.GKRProtocol.LookupNative.AddSubCached
namespace LookupImporterControl
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
'''
    result = compile_source(head + command('AddSubCached', 3) + '\nend LookupImporterControl\n')
    if result.returncode:raise SystemExit('Legacy importer:\n' + result.stdout[-1800:])
    print('PASS original legacy source lookup importer', flush=True)
    changes = [
        ('missing checker', command('AddSubCached', 5).replace(
            ' using_checks Airbender.Compiler.LookupSourceChecks.AddSubCached', ''), 'requires checker facts'),
        ('checker in input phase', command('AddSubCached', 4).rstrip() + ' using_checks Missing\n',
         'only the complete source lookup phase accepts'),
        ('unsupported phase', command('AddSubCached', 3).replace('phase 3', 'phase 9'),
         'unsupported source lookup import phase'),
    ]
    for label, source, expected in changes:
        result = compile_source(head + source + '\nend LookupImporterControl\n')
        if not result.returncode or expected not in result.stdout:
            raise SystemExit(label + ':\n' + result.stdout[-1800:])
        print('PASS source lookup phase control:', label, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericLookupSourceChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericFunctionalBaseChecks
namespace LookupSourceControl
set_option maxRecDepth 8192
private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩
def relations : List (Polynomial 1 Source.BaseField) := [[(1, [])]]
def zeroRecipe : NativeBaseRecipe := .constant 0
-- Source coefficients store one in Montgomery form.
def withWitness : BaseRecipeAgreement relations zeroRecipe :=
  ⟨.input (.Expression #[] ⟨⟨268435454, by decide⟩⟩), [([(1, [])], ⟨0, by decide⟩)]⟩
def withoutWitness : BaseRecipeAgreement relations zeroRecipe := {withWitness with witness := []}
def changedWitness : BaseRecipeAgreement relations zeroRecipe :=
  {withWitness with witness := [([(2, [])], ⟨0, by decide⟩)]}
def bank : WireBank 1 := ⟨fun _ => .BaseLayerWitness 7, fun _ => 0⟩
def badBank : WireBank 1 := ⟨fun _ => .BaseLayerWitness 8, fun _ => 0⟩
def place : Nat → Fin 1 := fun _ => 0
def inputRecipe : NativeBaseRecipe := .input (.BaseLayerWitness 7)
def inputAgreement : BaseRecipeAgreement relations inputRecipe := ⟨.input (.Variable 0), []⟩
'''
    source = 'NumericLookupSourceChecks.ofAgreement withWitness place bank'
    base = f'check babyBearModulus [encode ({source})] = true'
    changes = [] if args.case else [
        ('nonempty witness', base, base.replace('withWitness', 'withoutWitness'), ''),
        ('witness coefficient', base, base.replace('withWitness', 'changedWitness'), ''),
        ('bank round trip', 'check babyBearModulus [encode (NumericLookupSourceChecks.ofAgreement inputAgreement place bank)] = true',
         'check babyBearModulus [encode (NumericLookupSourceChecks.ofAgreement inputAgreement place badBank)] = true', ''),
        ('role flag', 'check babyBearModulus [encode (NumericLookupSourceChecks.ofFlag (n := 1) true)] = true',
         'check babyBearModulus [encode (NumericLookupSourceChecks.ofFlag (n := 1) false)] = true', ''),
        ('zero term binding', f'(encode ({source})).right = [(0, []), (1, [])]',
         f'(encode ({source})).right = [(1, [])]', ''),
    ]
    for case in args.case or CASES:
        owner = 'Airbender.Compiler.LookupSourceChecks.' + case
        for first in [0, len(descriptors(case)) - 1]:
            left = f'({owner}.data.drop {first}).take 1'
            right = f'(({owner}.originalEntries.drop {first}).take 1).map encode'
            changes.append((case + ' ' + str(first), left + ' = ' + right,
                '(' + left + ').drop 1 = ' + right,
                'import Airbender.Proofs.GKRProtocol.LookupSourceChecks.' + case + '.Data\n'))
    for label, exact, changed, imports in changes:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement + '\nend LookupSourceControl\n')
            if not mutated and result.returncode:raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1800:])
        print('PASS lookup source control:', label, flush=True)
    print('PASS', len(changes), 'exact controls; kernel rejects all mutations', flush=True)
    if not args.case:importer_controls()


if __name__ == '__main__':main()
