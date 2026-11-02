#!/usr/bin/env python3
"""Reject changed memory bindings, omitted operands and invalid importer phases."""
import argparse
from check_clean_argument_controls import compile_source
import gkr_packed_memory_payload as packed
import gkr_memory_certificate as legacy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=packed.CASES, action='append')
    parser.add_argument('--shared-only', action='store_true')
    args = parser.parse_args()
    if args.shared_only and args.case:
        parser.error('--shared-only cannot select a capture')
    prefix = '''import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.AddSubCached.Inputs
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericFunctionalBaseChecks
namespace MemoryPayloadControl
set_option maxRecDepth 8192
private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩
def relations (n : Nat) : List (Polynomial n Source.BaseField) := [[(1, [])]]
def field (n : Nat) : MemoryFieldAgreement (relations n) :=
  ⟨.constant 1, .constant 0, [([(1, [])], ⟨0, by simp [relations]⟩)]⟩
def missingWitness (n : Nat) : MemoryFieldAgreement (relations n) :=
  {field n with witness := []}
def badCoefficient (n : Nat) : MemoryFieldAgreement (relations n) :=
  {field n with witness := [([(2, [])], ⟨0, by simp [relations]⟩)]}
'''
    source = ('NumericMemoryPayloadChecks.ofField (field _) MemoryNative.AddSubCached.native.sourcePlacement '
              'MemoryNative.AddSubCached.native.bank ConsumerNative.AddSubCached.native.typing []')
    exact = 'check babyBearModulus [encode (' + source + ')] = true'
    changes = [] if args.case else [
        ('nonempty mask witness', exact, exact.replace('(field _)', '(missingWitness _)'), ''),
        ('mask witness coefficient', exact, exact.replace('(field _)', '(badCoefficient _)'), ''),
    ]
    for case in ([] if args.shared_only else args.case or packed.CASES):
        owner = 'Airbender.Compiler.MemoryPayloadChecks.' + case
        selected = list(packed.entries(case))
        imports = 'import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case + '.Data\n'
        # Check both ends and each distinct original predicate family.
        indices = sorted({0, len(selected) - 1} | {
            next(i for i, (label, _) in enumerate(selected) if label[0] == kind)
            for kind in ('expansion', 'ports', 'fingerprint', 'mask')})
        for index in indices:
            view = f'({owner}.data.drop {index}).take 1'
            if index == 0:
                piece = f'[{owner}.projectionData]'
            else:
                chunk, offset = (index - 1) // 4 * 4 + 1, (index - 1) % 4
                piece = f'({owner}.data{chunk}.drop {offset}).take 1'
                typed = '[encode (' + selected[index][1] + ')]'
                changes.append((case + ' source ' + str(index), piece + ' = ' + typed,
                                '(' + piece + ').drop 1 = ' + typed, imports))
            changes.append((case + ' view ' + str(index), view + ' = ' + piece,
                            '(' + view + ').drop 1 = ' + piece, imports))
        projection = f'{owner}.projectionData.ports'
        good = f'({projection}.drop 0).take 2 = ({owner}.projectionChunk0.getD 0 ⟨[], [], []⟩).ports.take 2'
        changes.append((case + ' projection ports', good, good.replace('.take 2 =', '.take 0 ='), imports))
    for label, good, bad, imports in changes:
        for mutated, statement in [(False, good), (True, bad)]:
            result = compile_source(imports + prefix + 'numeric_data_binding result : ' + statement
                                    + '\nend MemoryPayloadControl\n')
            if not mutated and result.returncode:
                raise SystemExit('Exact ' + label + ':\n' + result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed ' + label + ':\n' + result.stdout[-1800:])
        print('PASS memory payload:', label, flush=True)
    if not args.case:
        text = legacy.module(packed.capture_name('AddSubCached'), 'AddSubCached')[1]
        result = compile_source(text.replace('Airbender.Compiler.MemoryNative.AddSubCached', 'MemoryPayloadLegacy'))
        if result.returncode:
            raise SystemExit('Legacy memory importer:\n' + result.stdout[-1800:])
        print('PASS original memory importer', flush=True)
        text = packed.native('AddSubCached')[1].replace('Airbender.Compiler.MemoryNative.AddSubCached', 'MemoryPayloadBadPhase')
        for suffix in ['phase 0 using_checks MissingFacts', 'phase 1', 'phase 3']:
            broken = text.replace('phase 1 using_checks Airbender.Compiler.MemoryPayloadChecks.AddSubCached', suffix)
            result = compile_source(broken)
            if not result.returncode or not any(message in result.stdout for message in ['memory phase 1 requires', 'memory phase must']):
                raise SystemExit('Invalid memory phase:\n' + result.stdout[-1800:])
        print('PASS memory phase controls', flush=True)
        data = packed.inputs('AddSubCached').replace('Airbender.Compiler.MemoryNative.AddSubCached', 'MemoryPayloadBadFacts')
        wrong = packed.native('AddSubCached')[1].replace('Airbender.Compiler.MemoryNative.AddSubCached', 'MemoryPayloadBadFacts')
        wrong = wrong.replace('using_checks Airbender.Compiler.MemoryPayloadChecks.AddSubCached', 'using_checks MemoryPayloadWrongFacts')
        wrong = ('namespace MemoryPayloadWrongFacts\ntheorem projection : True := True.intro\n'
                 'end MemoryPayloadWrongFacts\n' + wrong[wrong.index('namespace MemoryPayloadBadFacts'):])
        result = compile_source(data + '\n' + wrong)
        if not result.returncode or not any(mark in result.stdout.lower() for mark in ['invalid projection', 'invalid field', 'type mismatch']):
            raise SystemExit('Wrong memory facts:\n' + result.stdout[-1800:])
        print('PASS memory finalizer rejects facts of the wrong type', flush=True)
        result = compile_source('''import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport
open Airbender.Compiler
opaque hidden : List NumericFunctionalBaseChecks.Data := []
numeric_functional_base_capture data := hidden
''')
        if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
            raise SystemExit('Opaque memory payload:\n' + result.stdout[-1800:])
        print('PASS strict importer rejects opaque memory data', flush=True)
    print('PASS', len(changes), 'exact/kernel mutation pairs', flush=True)


if __name__ == '__main__':
    main()
