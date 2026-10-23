#!/usr/bin/env python3
"""Exact bounded kernel replay of the complete compiled dependency DAG.

Each module is checked only after all its actual header imports have successful
identical-content ledger entries. Stock leanchecker prefix fanout and unchecked
project imports cannot establish a pass here. This is separate from axiom policy.
"""
import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import sys

from check_axioms import HERE, ROOT, run_guarded, sha, write_json


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def source_modules(root):
    modules = {'Airbender'}
    for directory in ['Airbender', 'Tests']:
        modules.update('.'.join(path.relative_to(root).with_suffix('').parts)
                       for path in (root / directory).rglob('*.lean'))
    generated = root / 'generated/sail-rv32'
    modules.update('.'.join(path.relative_to(generated).with_suffix('').parts)
                   for path in generated.rglob('*.lean'))
    return sorted(modules)


def tool_identity(sysroot, guard):
    paths = [HERE / 'KernelReplay.lean', HERE / 'check_kernel_replay.py', HERE / 'check_axioms.py',
             Path(guard), sysroot / 'bin/lean', sysroot / 'lib/lean/Lean/Replay.olean',
             sysroot / 'src/lean/Lean/Replay.lean', sysroot / 'src/lean/Lean/AddDecl.lean']
    paths += [sysroot / 'lib/lean/Lean/Replay.olean.server', sysroot / 'lib/lean/Lean/Replay.olean.private']
    for module in ['Lean/Replay', 'Lean/Environment', 'Lean/AddDecl', 'Lean/Util/FoldConsts']:
        ir = sysroot / 'lib/lean' / (module + '.ir')
        if ir.is_file():
            paths.append(ir)
    paths += sorted((sysroot / 'lib').rglob('*.dylib'))
    paths += sorted((sysroot / 'lib').rglob('*.so'))
    return {str(path): sha(path) for path in paths}


def run_replay(args, modules=None):
    root, output = args.root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    ledger = (args.ledger or output / 'ledger').resolve()
    ledger.mkdir(parents=True, exist_ok=True)
    (ledger / 'inventories').mkdir(exist_ok=True)
    (ledger / 'passed').mkdir(exist_ok=True)
    identities = tool_identity(args.sysroot.resolve(), args.guard.resolve())
    tool_key = digest({'files': identities, 'limits': [2560, 5120, 900], 'adapter': 1})
    selected = sorted(set(modules or args.module or source_modules(root)))
    scope = 'selected_modules' if modules or args.module else 'all_project_source_modules'
    extra = os.pathsep.join(map(str, args.extra_path))
    lean_path = extra + (os.pathsep + os.environ['LEAN_PATH'] if os.environ.get('LEAN_PATH') else '') if extra else None
    helper = ['lake', 'env', 'lean', '--run', str(root / 'scripts/KernelReplay.lean')]
    def job(label, command, expected_exit=0):
        return run_guarded(root, args.guard.resolve(), args.sysroot.resolve(), output / 'jobs', label,
                           command, expected_exit=expected_exit, lean_path=lean_path)
    try:
        job('search-path', helper + ['paths', str(output / 'search-path.json')])
        search_path = [Path(path).resolve() for path in json.loads((output / 'search-path.json').read_text())]
        def resolve(module):
            relative = Path(*module.split('.')).with_suffix('.olean')
            candidates = {str((path / relative).resolve()) for path in search_path if (path / relative).is_file()}
            if len(candidates) != 1:
                raise ValueError(f'Missing/ambiguous compiled module {module}: {sorted(candidates)}')
            exported = Path(next(iter(candidates)))
            server, private = Path(str(exported) + '.server'), Path(str(exported) + '.private')
            if server.exists() != private.exists():
                raise ValueError('Incomplete server/private artifact pair: ' + module)
            return [exported] + ([server, private] if server.exists() else [])
        replay_library = resolve('Lean.Replay')[0]
        if replay_library != (args.sysroot.resolve() / 'lib/lean/Lean/Replay.olean').resolve():
            raise ValueError('Checker implementation resolves outside the pinned toolchain')
        graph, frozen, stats = {}, dict(identities), {}
        def remember(path):
            path = Path(path)
            key = str(path)
            current = path.stat()
            signature = (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns, current.st_ctime_ns)
            if key in stats and signature != stats[key] and sha(path) != frozen[key]:
                raise ValueError('Frozen compiled artifact changed: ' + key)
            if key not in frozen:
                frozen[key] = sha(path)
            stats[key] = signature
            return frozen[key]
        def unchanged():
            for path in frozen:
                remember(path)
        pending = deque(selected)
        while pending:
            module = pending.popleft()
            if module in graph:
                continue
            files = resolve(module)
            parts = {str(path): remember(path) for path in files}
            inventory_key = digest({'tool': tool_key, 'module': module, 'parts': parts})
            inventory = ledger / 'inventories' / (inventory_key + '.json')
            if not inventory.is_file():
                unchanged()
                job('inspect-' + module, helper + ['inspect', module, str(inventory)])
                unchanged()
            data = json.loads(inventory.read_text())
            if (data.get('schema') != 'airbender-kernel-replay-v1' or data.get('module') != module
                    or [str(Path(path).resolve()) for path in data['files']] != list(parts)
                    or len(data['safe']) != len(set(data['safe']))
                    or {item['user'] for item in data.get('dependencies', [])} != set(data['safe'])
                    or len(data.get('dependencies', [])) != len(data['safe'])
                    or (data.get('isModule') is True and len(files) != 3)):
                raise ValueError('Inconsistent exact-module inventory: ' + module)
            imports = data['imports']
            if module in [item['module'] for item in imports]:
                raise ValueError('Module relabeled as its own imported dependency: ' + module)
            graph[module] = {'parts': parts, 'imports': imports, 'inventory': str(inventory),
                             'inventory_sha256': sha(inventory), 'safe_count': len(data['safe']),
                             'skipped_count': len(data['skipped'])}
            pending.extend(item['module'] for item in imports)
            write_json(output / 'state.json', {'phase': 'inventory', 'current': module, 'modules': len(graph)})
        # Topological order uses every recorded import, including meta/private and third parties.
        waiting = {module: {item['module'] for item in data['imports']} for module, data in graph.items()}
        users = {module: set() for module in graph}
        for module, dependencies in waiting.items():
            for dependency in dependencies:
                if dependency not in graph:
                    raise ValueError('Missing compiled dependency: ' + dependency)
                users[dependency].add(module)
        ready = deque(sorted(module for module, dependencies in waiting.items() if not dependencies))
        order = []
        while ready:
            module = ready.popleft()
            order.append(module)
            for user in sorted(users[module]):
                waiting[user].discard(module)
                if not waiting[user]:
                    ready.append(user)
        if len(order) != len(graph):
            raise ValueError('Cyclic/incomplete compiled import DAG')
        manifest = {'schema': 'airbender-replay-manifest-v1', 'scope': scope, 'roots': selected,
                    'tool_key': tool_key, 'tool_identity': identities, 'search_path': list(map(str, search_path)),
                    'modules': graph, 'order': order, 'compiled_environment_only': True}
        write_json(output / 'manifest.json', manifest)
        passed = {}
        coverage_path = output / 'coverage.sqlite3'
        coverage_path.unlink(missing_ok=True)
        coverage = sqlite3.connect(coverage_path)
        coverage.executescript('''
          CREATE TABLE checked(name TEXT PRIMARY KEY,module TEXT);
          CREATE TABLE skipped(name TEXT,module TEXT,unsafe INTEGER,partial INTEGER);
          CREATE INDEX skipped_name ON skipped(name);
          CREATE TABLE edge(user TEXT,dependency TEXT,PRIMARY KEY(user,dependency));
          CREATE INDEX reverse_edge ON edge(dependency);
        ''')
        for index, module in enumerate(order):
            unchanged()
            data = graph[module]
            inventory = json.loads(Path(data['inventory']).read_text())
            if sha(Path(data['inventory'])) != data['inventory_sha256']:
                raise ValueError('Replay inventory changed: ' + module)
            dependencies = {imp['module']: passed[imp['module']]['key'] for imp in data['imports']}
            key = digest({'tool': tool_key, 'module': module, 'parts': data['parts'],
                          'imports': data['imports'], 'dependencies': dependencies,
                          'inventory_sha256': data['inventory_sha256']})
            record = ledger / 'passed' / (key + '.json')
            result = json.loads(record.read_text()) if record.is_file() else None
            if result is not None:
                if (result.get('key') != key or result.get('status') != 'pass'
                        or result.get('safe') != inventory['safe'] or result.get('dependencies') != dependencies
                        or not result.get('guard', {}).get('passed')
                        or not Path(result.get('report', '')).is_file()
                        or sha(Path(result['report'])) != result.get('report_sha256')):
                    raise ValueError('Invalid saved replay ledger record: ' + module)
            else:
                report = output / ('replay-' + module + '.json')
                guard = job('replay-' + module, helper + ['replay', module, str(report)])
                unchanged()
                replayed = json.loads(report.read_text())
                if (replayed.get('status') != 'pass' or replayed.get('module') != module
                        or replayed.get('safe') != inventory['safe'] or replayed.get('imports') != inventory['imports']
                        or replayed.get('skipped') != inventory['skipped']):
                    raise ValueError('Kernel replay did not cover the exact safe module inventory: ' + module)
                saved_report = ledger / 'passed' / (key + '.report.json')
                saved_report.write_bytes(report.read_bytes())
                result = {'key': key, 'status': 'pass', 'module': module, 'parts': data['parts'],
                          'dependencies': dependencies, 'safe': inventory['safe'],
                          'skipped': inventory['skipped'], 'skippedDependencyUses': inventory['skippedDependencyUses'],
                          'guard': guard, 'report': str(saved_report), 'report_sha256': sha(saved_report)}
                write_json(record, result)
            passed[module] = result
            coverage.executemany('INSERT OR IGNORE INTO checked VALUES(?,?)', [(name, module) for name in inventory['safe']])
            coverage.executemany('INSERT INTO skipped VALUES(?,?,?,?)',
                                 [(item['name'], module, item['unsafe'], item['partial']) for item in inventory['skipped']])
            for item in inventory['dependencies']:
                coverage.executemany('INSERT OR IGNORE INTO edge VALUES(?,?)',
                                     [(item['user'], dependency) for dependency in item['uses']])
            coverage.commit()
            write_json(output / 'state.json', {'phase': 'replay', 'current': module, 'completed': index + 1, 'total': len(order)})
        uncovered = list(coverage.execute('''SELECT DISTINCT edge.dependency FROM edge
            LEFT JOIN checked ON checked.name=edge.dependency
            LEFT JOIN skipped ON skipped.name=edge.dependency
            WHERE checked.name IS NULL AND skipped.name IS NULL'''))
        if uncovered:
            raise ValueError('Safe declaration references an uninventoried dependency: ' + str(uncovered[:10]))
        skipped_use_count = 0
        with (output / 'skipped-dependency-uses.jsonl').open('w') as stream:
            for row in coverage.execute('''SELECT DISTINCT edge.user,edge.dependency,skipped.module,
                    skipped.unsafe,skipped.partial FROM edge JOIN skipped ON skipped.name=edge.dependency'''):
                stream.write(json.dumps(dict(zip(['user', 'dependency', 'module', 'unsafe', 'partial'], row))) + '\n')
                skipped_use_count += 1
        missing = []
        if args.axiom_result:
            audit_path = args.axiom_result.resolve()
            audit = json.loads(audit_path.read_text())
            if audit.get('passed') is not True:
                raise ValueError('The separate environment/axiom audit did not pass')
            database = audit_path.parent / 'dependencies.sqlite3'
            if sha(database) != audit.get('dependency_database_sha256'):
                raise ValueError('Audited dependency graph changed')
            audited_inputs = json.loads((audit_path.parent / 'inputs.json').read_text())
            if audited_inputs != {path: sha(Path(path)) for path in audited_inputs}:
                raise ValueError('Source/compiled inputs changed since the environment audit')
            coverage.execute('ATTACH DATABASE ? AS proofaudit', (str(database),))
            missing = list(coverage.execute('''SELECT decl.name,decl.origin FROM proofaudit.decl decl
                       LEFT JOIN checked ON checked.name=decl.name
                       WHERE decl.unsafe=0 AND decl.partial=0 AND checked.name IS NULL'''))
            if missing:
                raise ValueError('Required safe proof/type dependencies lack replay coverage: ' + str(missing[:10]))
        coverage.close()
        unchanged()
        # Final full byte comparison is independent of filesystem timestamps.
        if frozen != {path: sha(Path(path)) for path in frozen}:
            raise ValueError('Compiled artifact set changed at final closure')
        result = {'schema': 'airbender-replay-result-v1', 'passed': True, 'scope': scope, 'roots': selected,
                  'modules': len(graph), 'safe_declarations': sum(item['safe_count'] for item in graph.values()),
                  'skipped_declarations': sum(item['skipped_count'] for item in graph.values()),
                  'skipped_dependency_uses': skipped_use_count,
                  'codegen_only_names': sum(len(json.loads(Path(item['inventory']).read_text()).get('codegenOnly', [])) for item in graph.values()),
                  'axiom_audit_linked': bool(args.axiom_result), 'missing_safe_dependencies': missing,
                  'tool_key': tool_key, 'manifest_sha256': sha(output / 'manifest.json')}
        write_json(output / 'result.json', result)
        write_json(output / 'state.json', {'phase': 'complete', **result})
        print(json.dumps(result))
        return result
    except BaseException as error:
        write_json(output / 'state.json', {'phase': 'failed', 'error': str(error), 'scope': scope})
        # Never leave a stale completion certificate after an unsuccessful new run.
        (output / 'result.json').unlink(missing_ok=True)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--guard', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--ledger', type=Path)
    parser.add_argument('--module', action='append', default=[])
    parser.add_argument('--extra-path', type=Path, action='append', default=[])
    parser.add_argument('--axiom-result', type=Path)
    args = parser.parse_args()
    if not args.module and not args.axiom_result:
        parser.error('a complete project replay requires --axiom-result from the separate environment audit')
    run_replay(args)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, sqlite3.Error) as error:
        raise SystemExit(f'KERNEL_REPLAY_FAILED {error}') from error
