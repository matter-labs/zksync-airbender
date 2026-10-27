#!/usr/bin/env python3
"""Isolated, bounded positive/negative controls for proof inventory, axioms and replay.

False fixtures are copied only to a fresh temporary directory outside product
module roots. A compile/import/API/resource failure never counts as rejection of
a bad proof. Full transitive controls require the real full-DAG checker to run.
"""
import argparse
import json
from pathlib import Path
import re
import tempfile
from types import SimpleNamespace

from check_axioms import HERE, ROOT, analyze, run_guarded, write_json
from check_kernel_replay import run_replay


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--guard', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--ledger', type=Path)
    parser.add_argument('--direct-only', action='store_true')
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix='airbender-replay-negative-')).resolve()
    if scratch == root or root in scratch.parents:
        raise ValueError('Negative fixtures must be outside the production source tree')
    write_json(output / 'fixture-directory.json', {'directory': str(scratch)})
    mapping = {'ReplayGoodBase': 'ReplayGoodBase', 'ReplayGoodConsumer': 'ReplayGoodConsumer',
               'ReplayBadBase': 'ReplayBadBase', 'ReplayBadConsumer': 'ReplayBadConsumer',
               'NewAxiom': 'NewAxiom', 'AssuranceReview.Inventory': 'ProofInventory',
               'Tests.AssuranceUnusedAxiom': 'UnusedProjectAxiom',
               'AssuranceEntrypointLeft': 'EntrypointLeft',
               'Tests.AssuranceEntrypointRight': 'EntrypointRight'}
    stage = 'prepare'
    def job(label, command, expected_exit=0):
        return run_guarded(root, args.guard.resolve(), args.sysroot.resolve(), output, label,
                           command, expected_exit=expected_exit, lean_path=str(scratch))
    helper = ['lake', 'env', 'lean', '--run', str(root / 'scripts/KernelReplay.lean')]
    try:
        for module, template in mapping.items():
            stage = 'compile-' + module
            source = scratch.joinpath(*module.split('.')).with_suffix('.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text((HERE / 'fixtures' / (template + '.lean.in')).read_text())
            job(stage, ['lake', 'env', 'lean', '-R', str(scratch), '-o', str(source.with_suffix('.olean')), str(source)])
            if not source.with_suffix('.olean').is_file():
                raise ValueError('Control compilation produced no artifact: ' + module)
        for module, name in [('ReplayBadBase', 'bad'), ('ReplayBadConsumer', 'badConsumer')]:
            text = (output / ('compile-' + module + '.log')).read_text()
            pattern = "'AssuranceNegative." + name + "' does not depend on any axioms"
            if pattern not in text:
                raise ValueError('Injected false proof was not demonstrated axiom-free: ' + module)
        stage = 'inventory-kinds'
        request = {'modules': ['AssuranceReview.Inventory'],
                   'roots': ['OutsideNames.namedTheorem', 'OutsideNames.FieldDependency'],
                   'reviewPrefix': 'AssuranceReview'}
        write_json(output / 'inventory-request.json', request)
        job(stage, ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'),
                    str(output / 'inventory-request.json'), str(output / 'inventory.jsonl')])
        result = analyze(output / 'inventory.jsonl', request, {'commit': 'isolated-positive-control', 'roots': {}}, output / 'inventory-analysis')
        roots = result['roots']
        required = ['OutsideNames.namedTheorem', 'OutsideNames.proofDefinition', 'OutsideNames.proofAlias',
                    'OutsideNames.evidenceInstance', 'OutsideNames.generatedProof']
        if (not result['passed'] or any(name not in roots for name in required)
                or not any(name.endswith('.privateProof') for name in roots)
                or not any(name.startswith('OutsideNames.generatedProof.') for name in roots)
                or any(roots[name]['origin'] != 'AssuranceReview.Inventory' for name in roots)
                or 'OutsideNames.predicate' in roots or 'OutsideNames.ordinaryDefinition' in roots):
            raise ValueError('Origin/private/definition/instance/generated/predicate inventory controls failed')
        if 'Classical.choice' not in result['axioms'].get('OutsideNames.FieldDependency', []):
            raise ValueError('Environment audit omitted a constructor-field type dependency')
        stage = 'new-axiom-rejected'
        request = {'modules': ['NewAxiom'], 'roots': ['AssuranceNegative.usesForeign'], 'reviewPrefix': 'AssuranceReview'}
        write_json(output / 'axiom-request.json', request)
        job(stage, ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'),
                    str(output / 'axiom-request.json'), str(output / 'new-axiom.jsonl')])
        result = analyze(output / 'new-axiom.jsonl', request, {'commit': 'isolated-negative-control', 'roots': {}}, output / 'axiom-analysis')
        if (result['passed'] or result['forbidden_axioms'] != {'AssuranceNegative.usesForeign': ['AssuranceNegative.foreign']}
                or result['missing_baseline_roots'] or result['undispositioned_changes']):
            raise ValueError('New axiom did not fail specifically at the standard-axiom whitelist')
        stage = 'unused-project-axiom-rejected'
        request = {'modules': ['Tests.AssuranceUnusedAxiom'], 'roots': [], 'reviewPrefix': 'Airbender.Review'}
        write_json(output / 'unused-axiom-request.json', request)
        job(stage, ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'),
                    str(output / 'unused-axiom-request.json'), str(output / 'unused-axiom.jsonl')])
        result = analyze(output / 'unused-axiom.jsonl', request, {'commit': 'isolated-unused-control', 'roots': {}},
                         output / 'unused-axiom-analysis')
        if (result['passed'] or result['forbidden_project_axiom_declarations'] != ['Tests.AssuranceUnusedAxiom.unused']
                or result['roots'] or result['forbidden_axioms'] or result['missing_baseline_roots']
                or result['undispositioned_changes'] or result['unsafe_proof_dependencies']):
            raise ValueError('Unused Tests axiom did not fail specifically at the project-origin presence gate')
        # Independent executables may both export main. Inspect both complete
        # contexts and retain unused project axioms in the isolated context.
        stage = 'independent-entrypoint-unused-axiom-rejected'
        request = {'modules': ['AssuranceEntrypointLeft', 'Tests.AssuranceEntrypointRight'],
                   'entrypoints': ['AssuranceEntrypointLeft', 'Tests.AssuranceEntrypointRight'],
                   'roots': ['AssuranceEntrypoints.left', 'Tests.AssuranceEntrypointRight.right'],
                   'reviewPrefix': 'AssuranceReview'}
        write_json(output / 'entrypoint-request.json', request)
        job(stage, ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'),
                    str(output / 'entrypoint-request.json'), str(output / 'entrypoint.jsonl')])
        result = analyze(output / 'entrypoint.jsonl', request,
                         {'commit': 'isolated-entrypoint-control', 'roots': {}}, output / 'entrypoint-analysis')
        if (result['passed'] or set(result['roots']) != set(request['roots'])
                or result['forbidden_project_axiom_declarations'] != ['Tests.AssuranceEntrypointRight.unused']
                or result['forbidden_axioms'] or result['unsafe_proof_dependencies']
                or result['missing_baseline_roots'] or result['undispositioned_changes']):
            raise ValueError('Independent executable contexts lost roots or unused project axioms')
        stage = 'ambiguous-entrypoint-root-rejected'
        ambiguous = {**request, 'roots': ['main']}
        write_json(output / 'ambiguous-entrypoint-request.json', ambiguous)
        job(stage, ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'),
                    str(output / 'ambiguous-entrypoint-request.json'),
                    str(output / 'ambiguous-entrypoint.jsonl')], expected_exit=1)
        if 'ambiguous explicit audit root: main' not in (output / (stage + '.log')).read_text():
            raise ValueError('Ambiguous executable root failed for the wrong reason')
        for module in ['ReplayGoodBase', 'ReplayGoodConsumer', 'ReplayBadConsumer', 'NewAxiom']:
            stage = 'local-' + module
            job(stage, helper + ['replay', module, str(output / (stage + '.json'))])
            if json.loads((output / (stage + '.json')).read_text()).get('status') != 'pass':
                raise ValueError('Local positive/path control failed: ' + module)
        # A consumer-only success above is the import hazard, never a closure certificate.
        stage = 'direct-invalid-proof'
        job(stage, helper + ['replay', 'ReplayBadBase', str(output / 'must-not-pass.json')], expected_exit=1)
        text = (output / (stage + '.log')).read_text()
        if ('KERNEL_REPLAY_REJECTED ReplayBadBase' not in text or 'AssuranceNegative.bad' not in text
                or 'type mismatch' not in text.lower() or 'KERNEL_REPLAY_API_ERROR' in text
                or (output / 'must-not-pass.json').exists()):
            raise ValueError('Bad proof failed for a non-kernel/type reason')
        if not args.direct_only:
            ledger = args.ledger or output / 'full-dag-ledger'
            def dag(module, directory):
                options = SimpleNamespace(root=root, output=directory, ledger=ledger,
                                          guard=args.guard, sysroot=args.sysroot, extra_path=[scratch],
                                          module=[module], axiom_result=None)
                return run_replay(options)
            stage = 'full-dag-good-consumer'
            good = dag('ReplayGoodConsumer', output / 'good-dag')
            if good.get('passed') is not True:
                raise ValueError('Positive full-DAG control failed')
            stage = 'full-dag-bad-consumer'
            rejected = False
            try:
                dag('ReplayBadConsumer', output / 'bad-dag')
            except RuntimeError:
                metrics = output / 'bad-dag/jobs/replay-ReplayBadBase.result.json'
                log = output / 'bad-dag/jobs/replay-ReplayBadBase.log'
                if metrics.is_file() and log.is_file():
                    data = json.loads(metrics.read_text())
                    guards = data.get('metrics', [])
                    text = log.read_text()
                    rejected = (data.get('returncode') == 1 and len(guards) == 1
                                and guards[0].get('reason') == 'finished' and guards[0].get('exit') == 1
                                and guards[0].get('live_owned_after') == []
                                and 'KERNEL_REPLAY_REJECTED ReplayBadBase' in text
                                and 'AssuranceNegative.bad' in text and 'type mismatch' in text.lower()
                                and 'KERNEL_REPLAY_API_ERROR' not in text)
            if (not rejected or (output / 'bad-dag/result.json').exists()
                    or (output / 'bad-dag/replay-ReplayBadConsumer.json').exists()):
                raise ValueError('Transitive invalid proof was not rejected at its actual bad dependency')
        final = {'passed': True, 'scope': 'direct_controls_only' if args.direct_only else 'direct_and_full_transitive_controls',
                 'fixture_directory': str(scratch), 'transitive_unchecked': bool(args.direct_only),
                 'consumer_local_replay_demonstrated_import_hazard': True}
        write_json(output / 'controls-result.json', final)
        print(json.dumps(final))
        return 0
    except BaseException as error:
        (output / 'controls-result.json').unlink(missing_ok=True)
        write_json(output / 'controls-state.json', {'phase': 'failed', 'stage': stage, 'error': str(error), 'fixture_directory': str(scratch)})
        raise


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError) as error:
        raise SystemExit(f'ASSURANCE_CONTROL_FAILED {error}') from error
