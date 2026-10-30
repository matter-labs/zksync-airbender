#!/usr/bin/env python3
"""Guarded batched Lake freshness; audit/replay/fresh exports are separate.

Default scope checks every concrete Airbender, Tests and retained Sail module,
then the library, executable closures and static/runtime gates. --module limits
scope to selected project modules and their project-source dependencies. Every
build still uses Lake's normal dependency freshness; hashes never skip a target.
"""
import argparse
from collections import Counter
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
QUERY_LIMIT = 128
LAKE_NO_BUILD_EXIT = 3  # Pinned Lake.Build.Run.noBuildCode, not a compilation success.


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def discover(root):
    sources = {'Airbender': root / 'Airbender.lean'}
    for directory, base in [('Airbender', root), ('Tests', root), ('Scripts', root),
                            ('generated/sail-rv32', root / 'generated/sail-rv32')]:
        for path in sorted((root / directory).rglob('*.lean')):
            module = '.'.join(path.relative_to(base).with_suffix('').parts)
            if module in sources:
                raise ValueError('Duplicate project module: ' + module)
            sources[module] = path.resolve()
    if not all(path.is_file() for path in sources.values()):
        raise ValueError('Missing top-level Airbender source')
    return sources


def ordered(nodes, imports):
    nodes = set(nodes)
    dependencies = {name: set(imports[name]) & nodes for name in nodes}
    users = {name: [] for name in nodes}
    for name, deps in dependencies.items():
        for dependency in deps:
            users[dependency].append(name)
    ready = [name for name in nodes if not dependencies[name]]
    heapq.heapify(ready)
    result = []
    while ready:
        name = heapq.heappop(ready)
        result.append(name)
        for user in users[name]:
            dependencies[user].remove(name)
            if not dependencies[user]:
                heapq.heappush(ready, user)
    if len(result) != len(nodes):
        raise ValueError('Cyclic source import graph')
    return result


class Frozen:
    """Full initial/final byte checks; stat changes trigger content revalidation."""
    def __init__(self, paths):
        self.paths = sorted(set(Path(path).resolve() for path in paths))
        self.hashes = self.contents()
        self.stats = self.signature()
        self.verify(force=True)

    def contents(self):
        return {str(path): sha(path) if path.is_file() else None for path in self.paths}

    def signature(self):
        result = []
        for path in self.paths:
            if path.is_file():
                info = path.stat()
                result.append((str(path), info.st_dev, info.st_ino, info.st_size,
                               info.st_mtime_ns, info.st_ctime_ns))
            else:
                result.append((str(path), None))
        return result

    def verify(self, force=False):
        current = self.signature()
        if not force and current == self.stats:
            return
        for _ in range(3):
            contents = self.contents()
            after = self.signature()
            if current != after:
                current = after
                continue
            if contents != self.hashes:
                changed = [path for path in contents if contents[path] != self.hashes[path]]
                raise ValueError('Frozen inputs changed: ' + ', '.join(changed[:8]))
            self.stats = after
            return
        raise ValueError('Inputs repeatedly changed during byte validation')


def identity(path):
    path = Path(path).resolve()
    return {'path': str(path), 'sha256': sha(path)}


def script_inputs(root):
    return sorted(path.resolve() for path in (root / 'scripts').rglob('*')
                  if path.is_file() and path.suffix in {'.py', '.lean', '.in', '.json'})


class Runner:
    def __init__(self, root, guard, output, workers=4):
        self.root, self.guard, self.output, self.workers = root, guard, output, workers
        self.run_id = time.strftime('%Y%m%dT%H%M%S') + '-' + str(os.getpid())
        self.directory = output / 'runs' / self.run_id
        self.directory.mkdir(parents=True)
        (output / 'result.json').unlink(missing_ok=True)
        self.completed, self.child, self.stage = [], None, 'preflight'
        self.started = time.monotonic()
        self.frozen, self.records = [], {}
        self.last_query = None
        self.repair_count = 0
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, self.interrupted)

    def state(self, phase, **values):
        write_json(self.output / 'state.json', {'phase': phase, 'stage': self.stage,
                   'run': self.run_id, 'directory': str(self.directory), 'completed': self.completed,
                   'elapsed_s': round(time.monotonic() - self.started, 2), **values})

    def interrupted(self, sig, _frame):
        if self.child is not None and self.child.poll() is None:
            self.child.send_signal(signal.SIGTERM)
        raise InterruptedError('Interrupted by signal ' + str(sig))

    def run(self, label, command, review=False, pooled=False, allow_failure=False):
        self.stage = label
        for frozen in self.frozen:
            frozen.verify()
        log = self.directory / (label + '.log')
        command = [str(part) for part in command]
        invocation = ([sys.executable, '-m', 'scripts.compilation_pool.guard'] if pooled
                      else [sys.executable, str(self.guard)])
        invocation += ['--mib', '2560', '--resident-mib', '5120',
                       '--seconds', '1800' if review else '900']
        if pooled:
            invocation += ['--lean-workers', str(self.workers)]
        invocation += ['--log', str(log)]
        if review:
            invocation.append('--review')
        invocation += ['--', *command]
        write_json(self.directory / (label + '.command.json'), {'cwd': str(self.root), 'command': invocation})
        self.state('running', log=str(log), command=invocation)
        try:
            self.child = subprocess.Popen(invocation, cwd=self.root, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT, text=True)
            output, _ = self.child.communicate()
        except BaseException:
            if self.child is not None and self.child.poll() is None:
                self.child.send_signal(signal.SIGTERM)
                self.child.wait(timeout=30)
            raise
        finally:
            child = self.child
            self.child = None
        (self.directory / (label + '.guard.log')).write_text(output)
        metrics = []
        for line in output.splitlines():
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, dict) and 'reason' in value:
                metrics.append(value)
        record = {'stage': label, 'run': self.run_id, 'command': invocation,
                  'returncode': child.returncode, 'metrics': metrics, 'log': str(log)}
        self.records[label] = record
        write_json(self.directory / (label + '.result.json'), record)
        with (self.output / 'metrics.jsonl').open('a') as stream:
            stream.write(json.dumps(record) + '\n')
        if (len(metrics) != 1 or metrics[0].get('reason') != 'finished'
                or metrics[0].get('exit') != child.returncode
                or metrics[0].get('live_owned_after') != []
                or (child.returncode != 0 and not allow_failure)):
            raise RuntimeError('Guarded stage failed: ' + label)
        if pooled and child.returncode not in (0, LAKE_NO_BUILD_EXIT):
            raise RuntimeError('Unexpected pooled query exit: ' + label)
        if pooled and (metrics[0].get('lean_workers_limit') != self.workers
                       or not 0 <= metrics[0].get('lean_workers_peak', -1) <= self.workers):
            raise ValueError('Unexpected pooled guard worker receipt: ' + label)
        for frozen in self.frozen:
            frozen.verify()
        if child.returncode == 0:
            self.completed.append(label)
        return log

    @staticmethod
    def query_values(log, count, label):
        values = []
        for line in log.read_text().splitlines():
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, (list, str)) or value is None:
                values.append(value)
        if len(values) != count:
            raise ValueError('Unexpected Lake query result count: ' + label)
        return values

    def query_pool(self, label, chunks):
        if not chunks or any(not chunk or len(chunk) > QUERY_LIMIT for chunk in chunks):
            raise ValueError('Require nonempty bounded query chunks')
        manifest = self.directory / (label + '.pool-manifest.json')
        pool_output = self.directory / (label + '.pool')
        jobs = [{'label': label + '-chunk-' + str(index), 'cwd': str(self.root),
                 'argv': ['lake', '--no-cache', '--no-build', '--json', 'query', *targets],
                 'reserved_footprint_mib': 256, 'reserved_resident_mib': 1024,
                 'seconds': 900, 'dependencies': [], 'exclusive': False,
                 'allowed_exits': [0, LAKE_NO_BUILD_EXIT]}
                for index, targets in enumerate(chunks)]
        write_json(manifest, {'jobs': jobs})
        self.run(label, [sys.executable, '-m', 'scripts.compilation_pool.pool',
                        '--manifest', manifest, '--output', pool_output,
                        '--workers', str(self.workers)], pooled=True, allow_failure=True)
        result_path = pool_output / 'result.json'
        result = json.loads(result_path.read_text())
        if (result.get('workers_limit') != self.workers
                or not 1 <= result.get('concurrent_jobs_peak', 0) <= self.workers
                or result.get('manifest_sha256') != sha(manifest)):
            raise ValueError('Unexpected pool receipt: ' + label)
        results = result.get('jobs', [])
        by_label = {job['label']: job for job in results}
        if len(results) != len(jobs) or len(by_label) != len(jobs) or set(by_label) != {job['label'] for job in jobs}:
            raise ValueError('Incomplete query pool member coverage: ' + label)
        members, failed = [], []
        for index, (job, targets) in enumerate(zip(jobs, chunks)):
            actual = by_label[job['label']]
            log = Path(actual['log']).resolve()
            if (actual.get('argv') != job['argv'] or actual.get('cwd') != str(self.root)
                    or log != pool_output / (job['label'] + '.log')
                    or actual.get('exit') not in (0, LAKE_NO_BUILD_EXIT)):
                raise ValueError('Unexpected query pool member: ' + job['label'])
            if actual['exit'] == LAKE_NO_BUILD_EXIT:
                failed.append(targets)
                continue
            members.append({'label': job['label'], 'targets': targets,
                            'pool_job_index': next(i for i, value in enumerate(results) if value['label'] == job['label']),
                            'log': identity(log), 'values': self.query_values(log, len(targets), job['label'])})
        passed = not failed
        if (result.get('passed') is not passed
                or self.records[label]['returncode'] != (0 if passed else LAKE_NO_BUILD_EXIT)):
            raise ValueError('Query pool success receipt disagrees: ' + label)
        receipt = {'label': label,
                   'guard_command': identity(self.directory / (label + '.command.json')),
                   'guard_result': identity(self.directory / (label + '.result.json')),
                   'guard_log': identity(self.directory / (label + '.guard.log')),
                   'aggregate_log': identity(self.directory / (label + '.log')),
                   'pool_manifest': identity(manifest), 'pool_result': identity(result_path),
                   'members': members, 'member_count': len(members),
                   'target_count': sum(len(member['targets']) for member in members)}
        write_json(self.directory / (label + '.query-receipt.json'), {**receipt, 'passed': passed})
        return receipt, failed

    def repair_chunks(self, chunks):
        for targets in chunks:
            self.repair_count += 1
            label = 'stale-repair-' + str(self.repair_count)
            if len(targets) == 1:
                # A normal Lake leaf build traverses its real dependencies. This
                # remains exclusive under the original supplied serial guard.
                self.run(label, ['lake', '--no-cache', 'build', targets[0]])
            else:
                middle = len(targets) // 2
                _, failed = self.query_pool(label, [targets[:middle], targets[middle:]])
                self.repair_chunks(failed)

    def query(self, label, targets):
        if not targets:
            raise ValueError('Require at least one query target')
        chunks = [targets[index:index + QUERY_LIMIT] for index in range(0, len(targets), QUERY_LIMIT)]
        receipt, failed = self.query_pool(label, chunks)
        if failed:
            self.repair_chunks(failed)
            receipt, failed = self.query_pool(label + '-final', chunks)
            if failed:
                raise ValueError('Targets still stale after guarded normal repair: ' + label)
        self.last_query = {'kind': 'normal_lake_no_build_query', 'workers_limit': self.workers,
                           'target_count': len(targets), 'chunk_limit': QUERY_LIMIT,
                           'targets': targets, 'batches': [receipt]}
        return [value for member in receipt['members'] for value in member['values']]

    def freshness(self, label, modules, facets):
        targets = ['+' + module + ':' + facet for module in modules for facet in facets]
        values = self.query(label, targets)
        freshness = dict(self.last_query)
        freshness['modules'] = {}
        for member in freshness['batches'][0]['members']:
            for index, target in enumerate(member['targets']):
                module, facet = target[1:].rsplit(':', 1)
                address = {'batch': freshness['batches'][0]['label'], 'member': member['label'], 'target_index': index}
                if len(facets) == 1:
                    freshness['modules'][module] = address
                else:
                    freshness['modules'].setdefault(module, {})[facet] = address
        return values, freshness


def compiled_hashes(runner, label, paths):
    paths = sorted(set(map(str, paths)))
    traces = {re.sub(r'\.olean(?:\.server|\.private)?$', '.trace', path) for path in paths}
    sidecars = [path + '.hash' for path in paths if Path(path + '.hash').is_file()]
    runner.frozen.append(Frozen([*traces, *sidecars]))
    request, result = runner.directory / (label + '-request.json'), runner.directory / (label + '.json')
    write_json(request, paths)
    runner.frozen.append(Frozen([request]))
    runner.run(label, [sys.executable, 'scripts/check_olean_hashes.py',
                      '--request', str(request), '--output', str(result)])
    runner.frozen.append(Frozen([result]))
    return identity(result)


def external_objects(root, modules):
    libraries = [root / '.lake/build/lib/lean']
    libraries += sorted((root / '.lake/packages').glob('*/.lake/build/lib/lean'))
    result = {}
    for module in modules:
        relative = Path(*module.split('.')).with_suffix('.olean')
        candidates = {path.resolve() for base in libraries if (path := base / relative).is_file()}
        if len(candidates) != 1:
            raise ValueError('Missing/ambiguous external compiled module: ' + module)
        base = candidates.pop()
        result[module] = {suffix: {'path': str(part), 'sha256': sha(part) if part.is_file() else None}
                          for suffix in ('', '.server', '.private') for part in [Path(str(base) + suffix)]}
    return result


def build_snapshot(runner, sources, imports, input_hashes, objects, external, external_sources, freshness, hash_reports):
    snapshot = {'schema': 'airbender-serial-build-v2', 'root': str(runner.root), 'complete_project': True,
                'sources': {module: {'path': str(path), 'sha256': input_hashes[str(path)]}
                            for module, path in sources.items()},
                'inputs': input_hashes, 'objects': objects, 'freshness': freshness, 'imports': imports,
                'external_imports': external, 'external_sources': external_sources,
                'external_imports_scope': 'complete_workspace_import_closure_of_project_modules',
                'compiled_hash_reports': hash_reports,
                'external_freshness_basis': 'normal Lake --no-build dependency freshness of every final project olean query',
                'guard': identity(runner.guard),
                'checker': identity(Path(__file__).resolve()),
                'source_queue': str(runner.directory / 'source-queue.json'),
                'source_queue_sha256': sha(runner.directory / 'source-queue.json')}
    path = runner.directory / 'serial-build-snapshot.json'
    write_json(path, snapshot)
    return path


def direct_axioms(root, log, output):
    expected_list = re.findall(r'^#print axioms (\S+)\s*$', (root / 'Airbender/Checks/Axioms.lean').read_text(), re.M)
    pattern = r"^'(.+?)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    found = list(re.finditer(pattern, log.read_text(), re.M))
    reports = {match[1]: sorted(set((match[2] or '').replace(',', ' ').split())) for match in found}
    baseline = json.loads((root / 'scripts/axiom_baseline.json').read_text())
    prior = baseline['roots']
    result = {'scope': 'direct_explicit_axiom_smoke_test', 'baseline_commit': baseline['commit'],
              'roots': reports, 'missing_baseline_roots': sorted(prior.keys() - reports.keys()),
              'changed_baseline_reports': {name: {'before': prior[name], 'after': reports[name]}
                  for name in prior.keys() & reports.keys() if prior[name] != reports[name]},
              'missing_source_reports': sorted(set(expected_list) - reports.keys()),
              'extra_reports': sorted(reports.keys() - set(expected_list)),
              'duplicate_source_roots': sorted(name for name, count in Counter(expected_list).items() if count != 1),
              'duplicate_reports': sorted(name for name, count in Counter(match[1] for match in found).items() if count != 1),
              'forbidden_axioms': {name: sorted(set(axioms) - ALLOWED) for name, axioms in reports.items() if set(axioms) - ALLOWED}}
    # Imported inductive roots can omit constructor-field dependencies here.
    # Only the environment walk compares authoritative baseline axiom sets.
    failures = ('missing_baseline_roots', 'missing_source_reports', 'extra_reports',
                'duplicate_source_roots', 'duplicate_reports', 'forbidden_axioms')
    result['passed'] = not any(result[key] for key in failures)
    write_json(output, result)
    if not result['passed']:
        raise ValueError('Direct axiom smoke test inventory/standard-axiom check failed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--guard', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--module', action='append', default=[])
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    args = parser.parse_args()
    root, guard, output = args.root.resolve(), args.guard.resolve(), args.output.resolve()
    if not guard.is_file():
        parser.error('Missing supplied resource guard')
    if output == root or any(output.is_relative_to(root / group) for group in ('Airbender', 'Tests', 'Scripts', 'generated', 'scripts')):
        parser.error('Output directory must be outside product source directories')
    runner = Runner(root, guard, output, args.workers)
    try:
        sources = discover(root)
        if set(args.module) - sources.keys():
            raise ValueError('Unknown selected project module: ' + ', '.join(sorted(set(args.module) - sources.keys())))
        config = tomllib.loads((root / 'lakefile.toml').read_text())
        executables = config.get('lean_exe', [])
        if {(item['name'], item['root']) for item in executables} != {
                ('airbender_import', 'Airbender.Import.Main'),
                ('airbender_tests', 'Tests.ArtifactImport'),
                ('program_rows_oracle', 'Scripts.ProgramRowsOracle')}:
            raise ValueError('Executable inventory changed; review serial native coverage')
        source_names = sorted(sources)
        paths = list(sources.values()) + [root / name for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
        tools = script_inputs(root)
        for name in ('guard.py', 'pool.py'):
            if root / 'scripts/compilation_pool' / name not in tools:
                raise ValueError('Missing compilation pool implementation: ' + name)
        paths += tools + list((root / 'artifacts/setup').glob('*.json'))
        paths += [root / item['path'] for item in config.get('input_file', [])] + [guard]
        paths += [root / 'scripts/axiom_baseline.json', root / 'artifacts/setup/native-cargo.lock']
        for pattern in ('*/lakefile.toml', '*/lakefile.lean', '*/lean-toolchain'):
            paths += list((root / '.lake/packages').glob(pattern))
        provenance = json.loads((root / 'artifacts/setup/manifest.json').read_text())
        evidence = json.loads((root / 'artifacts/setup/native-evidence.json').read_text())
        sail = json.loads((root / 'generated/sail-rv32/provenance.json').read_text())
        repo = root.parent.parent
        paths += [repo / relative for relative in provenance['source_sha256']]
        paths += [repo / relative for relative in evidence['sources']]
        paths += [repo / relative for relative in sail['platform_parameterization']['airbender_evidence_sha256']]
        paths += [root / 'generated/sail-rv32/provenance.json']
        frozen = Frozen(paths)
        if any(value is None for value in frozen.hashes.values()):
            raise ValueError('Required source/configuration/evidence input missing')
        runner.frozen.append(frozen)
        write_json(runner.directory / 'inputs.json', frozen.hashes)
        values = runner.query('project-imports', ['+' + name + ':imports' for name in source_names])
        if any(not isinstance(value, list) or any(not isinstance(name, str) for name in value) for value in values):
            raise ValueError('Unexpected project imports result')
        imports = dict(zip(source_names, values))
        selected = set(args.module) if args.module else set(sources)
        pending = list(selected)
        while pending:
            for dependency in imports[pending.pop()]:
                if dependency in sources and dependency not in selected:
                    selected.add(dependency)
                    pending.append(dependency)
        queue = ordered(selected, imports)
        write_json(runner.directory / 'source-queue.json', {'scope': 'selected_modules' if args.module else 'complete_project',
                   'modules': queue, 'sources': {name: str(path) for name, path in sources.items()}, 'imports': imports})
        source_values, source_freshness = runner.freshness('source-freshness', queue, ['olean'])
        for module, value in zip(queue, source_values):
            expected = root / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
            if not isinstance(value, str) or (root / value).resolve() != expected.resolve():
                raise ValueError('Unexpected source freshness artifact: ' + module)
        artifacts, objects = [], {}
        for module in queue:
            base = root / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
            if not base.is_file():
                raise ValueError('Missing normally built project artifact: ' + module)
            objects[module] = {}
            for suffix in ('', '.server', '.private'):
                part = Path(str(base) + suffix)
                artifacts.append(part)
                objects[module][suffix] = {'path': str(part), 'sha256': sha(part) if part.is_file() else None}
        compiled = Frozen(artifacts)
        runner.frozen.append(compiled)
        write_json(runner.directory / 'validated-objects.json', objects)
        compiled_paths = [record['path'] for parts in objects.values() for record in parts.values()
                          if record['sha256'] is not None]
        hash_reports = {'project': compiled_hashes(runner, 'compiled-artifact-hashes', compiled_paths)}
        snapshot = None
        if not args.module:
            external_names = sorted(set(dependency for deps in imports.values() for dependency in deps) - sources.keys())
            closures = runner.query('external-closures', ['+' + name + ':transImports' for name in external_names]) if external_names else []
            if any(not isinstance(value, list) or any(not isinstance(name, str) for name in value) for value in closures):
                raise ValueError('Unexpected external workspace import closure')
            external_names = sorted(set(external_names).union(*(set(value) for value in closures)) - sources.keys())
            if external_names:
                runner.freshness('external-freshness', external_names, ['olean'])
            external = external_objects(root, external_names)
            values = runner.query('external-sources', ['+' + name + ':lean' for name in external_names]) if external_names else []
            external_sources = {}
            for module, value in zip(external_names, values):
                if not isinstance(value, str) or not (path := (root / value).resolve()).is_file():
                    raise ValueError('Missing external source identity: ' + module)
                external_sources[module] = {'path': str(path), 'sha256': sha(path)}
            paths = [record['path'] for parts in external.values() for record in parts.values()]
            paths += [record['path'] for record in external_sources.values()]
            external_frozen = Frozen(paths)
            runner.frozen.append(external_frozen)
            hash_reports['external'] = compiled_hashes(runner, 'workspace-artifact-hashes',
                [record['path'] for parts in external.values() for record in parts.values() if record['sha256'] is not None])
            for item in runner.frozen:
                item.verify(force=True)
            snapshot = build_snapshot(runner, sources, imports, frozen.hashes, objects, external, external_sources,
                                      source_freshness, hash_reports)
            runner.frozen.append(Frozen([snapshot]))
        native, native_freshness = {}, None
        if not args.module:
            roots = [item['root'] for item in executables]
            closures = runner.query('runtime-closures', ['+' + name + ':transImports' for name in roots])
            if any(not isinstance(value, list) or any(not isinstance(name, str) for name in value) for value in closures):
                raise ValueError('Unexpected native import-closure result')
            runtime = sorted(set(roots).union(*(set(value) for value in closures)))
            target_specs = [spec for name in runtime for spec in ('+' + name + ':imports', '+' + name + ':lean')]
            details = runner.query('runtime-inputs', target_specs)
            runtime_imports, runtime_sources = {}, {}
            for index, module in enumerate(runtime):
                deps, source = details[2 * index:2 * index + 2]
                if not isinstance(deps, list) or any(not isinstance(name, str) for name in deps) or not isinstance(source, str):
                    raise ValueError('Unexpected runtime module inventory: ' + module)
                runtime_imports[module] = deps
                path = (root / source).resolve()
                if not path.is_file():
                    raise ValueError('Missing runtime source: ' + module)
                runtime_sources[module] = path
            if any(set(deps) - set(runtime) for deps in runtime_imports.values()):
                raise ValueError('Incomplete actual executable workspace import closure')
            runtime_frozen = Frozen(list(runtime_sources.values()))
            runner.frozen.append(runtime_frozen)
            native_queue = ordered(runtime, runtime_imports)
            write_json(runner.directory / 'native-queue.json', {'roots': roots, 'modules': native_queue,
                       'sources': {name: str(path) for name, path in runtime_sources.items()}, 'imports': runtime_imports,
                       'input_sha256': runtime_frozen.hashes})
            native_values, native_freshness = runner.freshness('native-freshness', native_queue, ['o', 'olean'])
            write_json(runner.directory / 'native-freshness.json', native_freshness)
            for index, module in enumerate(native_queue):
                values = native_values[2 * index:2 * index + 2]
                if (any(not isinstance(value, str) for value in values)
                        or not (path := (root / values[0]).resolve()).is_file()
                        or not (olean := (root / values[1]).resolve()).is_file()):
                    raise ValueError('Normal Lake native/compiled target produced no artifact: ' + module)
                parts = {str(part): sha(part) if part.is_file() else None
                         for suffix in ('', '.server', '.private')
                         for part in [Path(str(olean) + suffix)]}
                native[module] = {'path': str(path), 'sha256': sha(path), 'compiled_parts': parts}
            native_paths = [record['path'] for record in native.values()]
            native_paths += [path for record in native.values() for path in record['compiled_parts']]
            native_frozen = Frozen(native_paths)
            runner.frozen.append(native_frozen)
            write_json(runner.directory / 'native-objects.json', native)
            compiled_hashes(runner, 'native-compiled-artifact-hashes',
                [path for record in native.values() for path, value in record['compiled_parts'].items() if value is not None])
            runner.run('library', ['lake', '--no-cache', 'build', 'Airbender'])
            for item in executables:
                runner.run('executable-' + item['name'], ['lake', '--no-cache', 'build', item['name']])
            log = runner.run('direct-axioms', ['lake', 'env', 'lean', '-j1', '-DElab.async=false', 'Airbender/Checks/Axioms.lean'])
            runner.stage = 'direct-axioms-comparison'
            direct_axioms(root, log, runner.directory / 'direct-axioms-comparison.json')
            runner.run('importer-runtime', ['lake', 'exe', 'airbender_tests'])
            for label, script in [('setup-source-identity', 'check_setup_artifacts.py'),
                                  ('compiler-source-identity', 'check_gkr_translations.py'),
                                  ('native-window-semantics', 'check_gkr_window_semantics.py'),
                                  ('native-evidence', 'check_native_evidence.py'),
                                  ('sail-reference', 'check_sail_reference.py'),
                                  ('proof-boundaries', 'check_proof_boundaries.py')]:
                runner.run(label, [sys.executable, 'scripts/' + script])
            runner.run('native-lookup-bindings',
                       [sys.executable, 'scripts/generate_native_lookup_requests.py', '--check'])
            runner.run('setup-source-generation',
                       [sys.executable, 'scripts/generate_setup_source_banks.py', '--check'])
            runner.run('setup-source-byte-identity',
                       ['lake', 'env', sys.executable, 'scripts/check_setup_source_banks.py'])
            runner.run('theta-fragment-correspondences',
                       [sys.executable, 'scripts/generate_theta_fragment_maps.py', '--check'])
            runner.run('review', [sys.executable, 'scripts/check_review.py', '--verified-build', str(snapshot)], review=True)
        runner.stage = 'closure'
        if discover(root) != sources:
            raise ValueError('Project source inventory changed during verification')
        if script_inputs(root) != tools:
            raise ValueError('Recursive tool input inventory changed during verification')
        for item in runner.frozen:
            item.verify(force=True)
        binaries = {}
        if not args.module:
            for executable in executables:
                path = root / '.lake/build/bin' / executable['name']
                if not path.is_file():
                    raise ValueError('Missing built executable: ' + executable['name'])
                binaries[executable['name']] = {'path': str(path), 'sha256': sha(path)}
        result = {'passed': True, 'scope': 'selected_modules' if args.module else 'complete_source_and_runtime_gates',
                  'modules': len(queue), 'concrete_tests': sum(name.startswith('Tests.') for name in selected),
                  'retained_sail_modules': sum(name.startswith('SailRV32') for name in selected),
                  'runtime_native_modules': len(native), 'completed': runner.completed,
                  'workers_limit': args.workers, 'source_freshness_kind': source_freshness['kind'],
                  'native_freshness': identity(runner.directory / 'native-freshness.json') if native_freshness else None,
                  'directory': str(runner.directory), 'input_manifest': str(runner.directory / 'inputs.json'),
                  'input_manifest_sha256': sha(runner.directory / 'inputs.json'),
                  'compiled_manifest': str(runner.directory / 'validated-objects.json'),
                  'compiled_manifest_sha256': sha(runner.directory / 'validated-objects.json'),
                  'verified_build_snapshot': str(snapshot) if snapshot else None, 'executables': binaries,
                  'separate_required_gates': ['environment_axiom_audit', 'full_kernel_replay', 'native25_freshness']}
        write_json(output / 'result.json', result)
        runner.state('complete', result=str(output / 'result.json'))
        print(json.dumps(result))
        return 0
    except BaseException as error:
        (output / 'result.json').unlink(missing_ok=True)
        runner.state('interrupted' if isinstance(error, InterruptedError) else 'failed', error=str(error))
        raise


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        raise SystemExit('LEAN_CHECK_FAILED ' + str(error)) from error
