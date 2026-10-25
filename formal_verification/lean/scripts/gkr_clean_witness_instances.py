#!/usr/bin/env python3
"""Compose retained Clean constraints with the same full native trace witness."""
import argparse
import os
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_clean_links import MODELS, WIDTHS


def module(case, model, width):
    framed = 'Airbender.Compiler.FramedWitnessNative.' + case
    lookup = 'Airbender.Compiler.MaterializedWitnessNative.' + case
    closed = 'Airbender.Compiler.CleanClosedNative.' + case
    clean = 'Airbender.Compiler.CleanArithmeticNative.' + case + '.native'
    text = (LEAN / 'GKRProtocol/FramedWitnessNative' / (case + '.lean')).read_text()
    start = text.index('theorem complete_trace_extends')
    stop = text.index(' := by', start)
    theorem = text[start:stop]
    header, result = theorem.split(' :\n', 1)
    header = header.replace('theorem complete_trace_extends', 'theorem complete_trace_clean_extends')
    domain = 'Airbender.Compiler.MaterializedNative.' + case + '.native.model.imported.data.length'
    header += f'\n    (data : Fin {domain} → ProverData Source.BaseField)'
    operations = f'(Airbender.{model}.clockConstraints (p := babyBearModulus)' + (f' {closed}.nativeSetup)' if width else ')')
    full = f'FlatOperation.ConstraintsHoldFlat ({clean}.environment (baseValue row) (data row)) {operations}'
    before, cancel = result.split('        ∀ group : ', 1)
    result = before + '        (∀ group : ' + cancel + ') ∧\n        ∀ row, ' + full
    body = (f'  obtain ⟨counts, constructed⟩ := {framed}.complete_trace_extends sourceValue original clockValid primitives authored fallback\n'
            '  refine ⟨counts, ?_⟩\n  intro R _ hom challenges gamma\n'
            '  obtain ⟨baseValue, values, correct, cancel⟩ := constructed hom challenges gamma\n'
            '  refine ⟨baseValue, values, correct, cancel, ?_⟩\n  intro row\n'
            '  have witness := (correct row).1\n'
            '  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩\n'
            f'  exact {closed}.retained_clock_from_source (sourceValue row) (counts row) (baseValue row) (data row)\n'
            '    inputsAt arithmetic helpers (authored row)\n')
    namespace = 'Airbender.Compiler.CleanWitnessNative.' + case
    content = (f'import GKRProtocol.CleanClosedNative.{case}\nimport GKRProtocol.FramedWitnessNative.{case}\n\n'
               f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
               f'open {lookup} {framed}\n'
               'set_option warningAsError true\nset_option Elab.async false\n'
               'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n' +
               header + ' :\n' + result + ' := by\n' + body + f'\nend {namespace}\n')
    return 'GKRProtocol.CleanWitnessNative.' + case, content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem, model, width in zip(FAMILIES, CASES, MODELS, WIDTHS, strict=True):
        if args.family and family not in args.family:
            continue
        if not width and family not in ['add-sub', 'jump-branch', 'mul-div', 'shift-binop']:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, text = module(stem + mode.title(), model, width)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('retained Clean witness composition changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(target, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
