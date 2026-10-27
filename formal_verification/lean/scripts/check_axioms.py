#!/usr/bin/env python3
"""Audit actual environment-origin proofs and preserve every established audit root.

Run normal dependency-aware Lean builds first. This checks compiled environments;
independent kernel replay is a separate gate. No source theorem regex chooses the
Review roots, and no imported cached axiom summary supplies dependency evidence.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import sqlite3
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_bytes(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix='.' + path.name + '.', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(value)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def write_json(path, value):
    write_bytes(path, (json.dumps(value, indent=2) + '\n').encode())


def run_guarded(root, guard, sysroot, directory, label, command, expected_exit=0, lean_path=None, stack_mib=None):
    """One owned heavy child, using the caller's unchanged global bounded worker."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / (label + '.log')
    env = dict(os.environ, LEAN_SYSROOT=str(sysroot))
    if lean_path is not None:
        env['LEAN_PATH'] = lean_path
        # Lake prepends its paths; runtime helpers must prepend isolated paths
        # after initSearchPath so an existing package root cannot shadow them.
        env['AIRBENDER_ASSURANCE_PATH'] = lean_path
    args = [sys.executable, str(guard), '--mib', '2560', '--resident-mib', '5120',
            '--seconds', '900', '--log', str(log)]
    if stack_mib is not None:
        args += ['--stack-mib', str(stack_mib)]
    args += ['--', *map(str, command)]
    write_json(directory / (label + '.command.json'), {'cwd': str(root), 'command': args,
               'environment': {key: env[key] for key in ('LEAN_SYSROOT', 'LEAN_PATH', 'AIRBENDER_ASSURANCE_PATH') if key in env}})
    def interrupted(signum, _frame):
        raise InterruptedError(f'signal {signum}')
    prior = {sig: signal.signal(sig, interrupted) for sig in [signal.SIGTERM, signal.SIGINT, signal.SIGHUP]}
    child = None
    try:
        child = subprocess.Popen(args, cwd=root, env=env, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        try:
            output, _ = child.communicate()
        except BaseException:
            if child.poll() is None:
                child.send_signal(signal.SIGTERM)
            cleanup, _ = child.communicate(timeout=30)
            (directory / (label + '.interrupted-guard.log')).write_text(cleanup)
            write_json(directory / (label + '.interrupted.json'), {
                'returncode': child.returncode,
                'metrics': [json.loads(line) for line in cleanup.splitlines()
                            if line.startswith('{')],
                'log': str(log),
            })
            raise
    finally:
        for sig, handler in prior.items():
            signal.signal(sig, handler)
    (directory / (label + '.guard.log')).write_text(output)
    records = [json.loads(line) for line in output.splitlines() if line.startswith('{')]
    metrics = [item for item in records if 'reason' in item and 'live_owned_after' in item]
    passed = (child.returncode == expected_exit and len(metrics) == 1
              and metrics[0].get('reason') == 'finished' and metrics[0].get('exit') == expected_exit
              and metrics[0].get('live_owned_after') == [])
    result = {'passed': passed, 'returncode': child.returncode, 'metrics': metrics, 'log': str(log)}
    write_json(directory / (label + '.result.json'), result)
    if not passed:
        raise RuntimeError(f'{label}: bounded worker/API/resource failure; see {log}')
    return result


def analyze(report, request, baseline, output, dispositions=None):
    """Use disk-backed graph traversal so the whole imported graph need not fit Python RAM."""
    output.mkdir(parents=True, exist_ok=True)
    database = output / 'dependencies.sqlite3'
    database.unlink(missing_ok=True)
    con = sqlite3.connect(database)
    con.executescript('''
      CREATE TABLE decl(name TEXT PRIMARY KEY, kind TEXT, origin TEXT, unsafe INTEGER, partial INTEGER);
      CREATE TABLE edge(user TEXT, dependency TEXT, PRIMARY KEY(user, dependency));
      CREATE INDEX reverse_edge ON edge(dependency);
      CREATE TABLE root(name TEXT PRIMARY KEY, origin TEXT, explicit INTEGER, proof INTEGER);
    ''')
    nonproof, present, header, footer = [], [], None, None
    with report.open() as stream:
        for line in stream:
            record = json.loads(line)
            kind = record['kind']
            if footer is not None:
                raise ValueError('Trailing data after audit footer')
            if kind == 'header':
                if header is not None or record.get('schema') != 'airbender-proof-audit-v1':
                    raise ValueError('Invalid/duplicate audit header')
                header = record
            elif header is None:
                raise ValueError('Audit report lacks a header')
            elif kind == 'root':
                con.execute('INSERT INTO root VALUES(?,?,?,?)',
                            (record['name'], record['origin'], record['explicit'], record['proofValued']))
            elif kind == 'declaration':
                con.execute('INSERT INTO decl VALUES(?,?,?,?,?)',
                            (record['name'], record['declarationKind'], record['origin'], record['unsafe'], record['partial']))
                con.executemany('INSERT INTO edge VALUES(?,?)', [(record['name'], dep) for dep in record['uses']])
            elif kind == 'review_nonproof':
                nonproof.append(record['name'])
            elif kind == 'present_axiom':
                present.append({'name': record['name'], 'origin': record['origin']})
            elif kind == 'footer':
                footer = record
            else:
                raise ValueError('Unknown audit record kind: ' + kind)
    roots = {name: {'origin': origin, 'explicit': bool(explicit), 'proofValued': bool(proof)}
             for name, origin, explicit, proof in con.execute('SELECT * FROM root')}
    count = con.execute('SELECT COUNT(*) FROM decl').fetchone()[0]
    if (header is None or footer is None or footer.get('roots') != len(roots)
            or footer.get('declarations') != count or header.get('explicitRoots') != len(request['roots'])
            or header.get('reviewPrefix') != request['reviewPrefix']):
        raise ValueError('Incomplete audit inventory')
    explicit = {name for name, item in roots.items() if item['explicit']}
    if explicit != set(request['roots']) or len(explicit) != len(request['roots']):
        raise ValueError('Explicit source-root inventory differs from actual environment audit')
    missing = [name for (name,) in con.execute('SELECT DISTINCT dependency FROM edge WHERE dependency NOT IN (SELECT name FROM decl)')]
    missing += [name for (name,) in con.execute('SELECT name FROM root WHERE name NOT IN (SELECT name FROM decl)')]
    if missing:
        raise ValueError('Missing dependency declarations: ' + ', '.join(missing[:10]))
    def users(name, proofs_only=False):
        suffix = ' AND root.proof=1' if proofs_only else ''
        query = '''WITH RECURSIVE reachable(name) AS
                   (VALUES (?) UNION SELECT edge.user FROM edge JOIN reachable ON edge.dependency=reachable.name)
                   SELECT root.name FROM root JOIN reachable ON root.name=reachable.name WHERE 1=1''' + suffix
        return [row[0] for row in con.execute(query, (name,))]
    axiom_sets = {name: [] for name in roots}
    for (name,) in con.execute("SELECT name FROM decl WHERE kind='axiom'").fetchall():
        for user in users(name):
            axiom_sets[user].append(name)
    unsafe_uses = {}
    for (name,) in con.execute('SELECT name FROM decl WHERE unsafe=1 OR partial=1').fetchall():
        reached = users(name, proofs_only=True)
        if reached:
            unsafe_uses[name] = reached
    for values in axiom_sets.values():
        values.sort()
    old = baseline['roots']
    changes = {name: {'before': old[name], 'after': axiom_sets[name]}
               for name in old if name in axiom_sets and old[name] != axiom_sets[name]}
    decisions = dispositions or {}
    unexplained = {name: item for name, item in changes.items()
                   if decisions.get(name, {}).get('before') != item['before']
                   or decisions.get(name, {}).get('after') != item['after']
                   or not isinstance(decisions.get(name, {}).get('reason'), str)
                   or not decisions[name]['reason'].strip()}
    forbidden = {name: sorted(set(values) - ALLOWED) for name, values in axiom_sets.items() if set(values) - ALLOWED}
    result = {'schema': 'airbender-axiom-result-v1', 'baseline_commit': baseline['commit'],
              'baseline_roots': len(old), 'roots': roots, 'axioms': axiom_sets,
              'review_nonproof': sorted(nonproof), 'present_axioms': present,
              'review_proof_roots': sorted(name for name, item in roots.items() if item['proofValued']
                                          and (item['origin'] == request['reviewPrefix']
                                               or item['origin'].startswith(request['reviewPrefix'] + '.'))),
              'new_explicit_roots': sorted(explicit - old.keys()),
              'forbidden_project_axiom_declarations': sorted(item['name'] for item in present
                  if any(item['origin'] == project or item['origin'].startswith(project + '.')
                         for project in ('Airbender', 'Tests'))),
              'missing_baseline_roots': sorted(set(old) - roots.keys()), 'changed_reports': changes,
              'undispositioned_changes': unexplained, 'forbidden_axioms': forbidden,
              'unsafe_proof_dependencies': unsafe_uses, 'declarations': count,
              'inventory_sha256': sha(report), 'compiled_environment_only': True}
    result['passed'] = not any(result[key] for key in ['missing_baseline_roots', 'undispositioned_changes',
                                                      'forbidden_axioms', 'unsafe_proof_dependencies',
                                                      'forbidden_project_axiom_declarations'])
    con.commit()
    con.close()
    result['dependency_database_sha256'] = sha(database)
    write_json(output / 'axiom-result.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--guard', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, default=HERE / 'axiom_baseline.json')
    parser.add_argument('--dispositions', type=Path, default=HERE / 'axiom_dispositions.json')
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    # Import every project source, including unused modules, so an unused project
    # axiom cannot evade the presence gate. Proof root selection remains by origin.
    sources = {root / 'Airbender.lean'}
    sources.update((root / 'Airbender').rglob('*.lean'))
    sources.update((root / 'Tests').rglob('*.lean'))
    modules = sorted('.'.join(path.relative_to(root).with_suffix('').parts) for path in sources)
    roots = re.findall(r'^#print axioms (\S+)\s*$', (root / 'Airbender/Checks/Axioms.lean').read_text(), re.M)
    request = {'modules': modules, 'roots': roots, 'reviewPrefix': 'Airbender.Review'}
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / 'request.json', request)
    paths = [root / 'lakefile.toml', root / 'lake-manifest.json', root / 'lean-toolchain']
    paths += [root.joinpath(*module.split('.')).with_suffix('.lean') for module in modules]
    for module in [*modules, 'Airbender.Checks.ProofInventory']:
        obj = root / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        if not obj.is_file():
            raise ValueError('Build this module normally before the audit: ' + module)
        paths += [path for suffix in ['', '.server', '.private']
                  if (path := Path(str(obj) + suffix)).is_file()]
    paths += [root / 'scripts/ProofAudit.lean', root / 'scripts/check_axioms.py',
              root / 'Airbender/Checks/ProofInventory.lean', args.guard.resolve()]
    paths += [args.baseline.resolve()]
    if args.dispositions:
        paths.append(args.dispositions.resolve())
    snapshot = {str(path): sha(path) for path in paths}
    write_json(output / 'inputs.json', snapshot)
    report = output / 'inventory.jsonl'
    run_guarded(root, args.guard.resolve(), args.sysroot.resolve(), output, 'environment-audit',
                ['lake', 'env', 'lean', '--run', str(root / 'scripts/ProofAudit.lean'), str(output / 'request.json'), str(report)])
    if snapshot != {str(path): sha(path) for path in paths}:
        raise ValueError('Audit source/compiled inputs changed during inspection')
    result = analyze(report, request, json.loads(args.baseline.read_text()), output,
                     json.loads(args.dispositions.read_text()) if args.dispositions else None)
    print(json.dumps({'passed': result['passed'], 'roots': len(result['roots']),
                      'baseline_roots': result['baseline_roots'], 'report': str(output / 'axiom-result.json')}))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, sqlite3.Error) as error:
        raise SystemExit(f'AXIOM_CHECK_FAILED {error}') from error
