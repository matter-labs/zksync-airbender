#!/usr/bin/env python3
"""Check public Review theorem audit coverage and the review guide's references."""

from pathlib import Path
import argparse
import hashlib
import json
import math
from collections import deque
import re
import subprocess
import tempfile
import tomllib
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent
GUIDES = tuple(ROOT / name for name in (
    "README.md", "VERIFICATION_STATUS.md", "TRUST_AND_REVIEW.md",
    "FORMAL_VERIFICATION_PLAN.md", "FINDINGS.md",
    "artifacts/setup/README.md", "generated/sail-rv32/README.md",
)) + tuple(sorted((ROOT / "Airbender/Review").rglob("README.md")))
# File names, source-only Rust/Sail names, and prose are not emitted Lean declarations.
SOURCE_NAMES = {
    "Model.lean", "extracted_base_pc.sail", "lakefile.toml", "av_gkr_compiler",
    "inits_or_teardowns_as_flattened_relation", "mask_read_for_witness",
    "run_hart_active", "F_Base", "FormalCircuit", "sorry",
}


def guide_references(guide):
    text = re.sub(r"```.*?```", "", guide.read_text(), flags=re.S)
    source_names = SOURCE_NAMES | {
        name for entry in re.findall(r"<!--\s*source-names:\s*(.*?)-->", text, re.S)
        for name in entry.split()
    }
    return {name for name in re.findall(r"`([^`\n]+)`", text)
            if re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", name)
            and name not in source_names
            and not re.fullmatch(r"[0-9a-f]{40}", name)}


def guide_names():
    return set().union(*(guide_references(guide) for guide in GUIDES))


def module_for_link(guide, target):
    link = urlsplit(target.strip("<>"))
    if link.scheme or not link.path.endswith(".lean"):
        return None
    path = (guide.parent / unquote(link.path)).resolve()
    try:
        relative = path.relative_to(ROOT)
    except ValueError:
        return None
    parts = relative.with_suffix("").parts
    if parts[:2] == ("generated", "sail-rv32"):
        return ".".join(parts[2:])
    if parts and parts[0] in {"Airbender", "Tests"}:
        return ".".join(parts)
    if relative == Path("scripts/SailPlatform.lean"):
        return "SailRV32.SailPlatform"
    return None


def guide_context(guide):
    """Linked Lean files and explicit module annotations are declaration contexts.

    A short name may resolve only inside these origin modules. Reexport/import
    closure is deliberately not a context: it would make an audit-root link
    silently admit the whole environment.
    """
    text = guide.read_text()
    modules = {module for target in re.findall(r"\[[^]\n]*\]\(([^)\n]+)\)", text)
               if (module := module_for_link(guide, target)) is not None}
    modules.update(module for entry in re.findall(r"<!--\s*lean-context:\s*(.*?)-->", text, re.S)
                   for module in entry.split())
    return modules


def resolve_reference(reference, candidates, modules):
    # A full declaration name is already an explicit declaration context.
    exact = {name for name, _ in candidates if name == reference}
    matches = exact or {name for name, module in candidates if module in modules}
    if len(matches) != 1:
        kind = "ambiguous" if matches else "missing"
        raise ValueError(f"{kind} declaration {reference} in explicit context: "
                         + ", ".join(sorted(matches)))
    return next(iter(matches))


def check_references(output):
    candidates = {}
    for reference, name, module in re.findall(r"^DOC_DECL (\S+) (\S+) (\S+)$", output, re.M):
        candidates.setdefault(reference, set()).add((name, module))
    count = 0
    errors = []
    for guide in GUIDES:
        modules = guide_context(guide)
        for reference in sorted(guide_references(guide)):
            try:
                resolve_reference(reference, candidates.get(reference, set()), modules)
            except ValueError as error:
                errors.append(f"{guide.relative_to(ROOT)}: {error}")
            else:
                count += 1
    check_reference_controls(candidates)
    if errors:
        raise ValueError(f"{len(errors)} guide declaration errors:\n" + "\n".join(errors))
    return count


def check_reference_controls(candidates):
    """Use actual compiled declarations to exercise ambiguity and wrong contexts."""
    for reference, entries in candidates.items():
        by_module = {}
        for name, module in entries:
            by_module.setdefault(module, set()).add(name)
        choices = [(module, next(iter(names))) for module, names in by_module.items()
                   if len(names) == 1 and reference not in names]
        if len(choices) >= 2:
            first, second = sorted(choices)[:2]
            if resolve_reference(reference, entries, {first[0]}) != first[1]:
                raise ValueError("Contextual reference positive control failed")
            try:
                resolve_reference(reference, entries, {first[0], second[0]})
            except ValueError as error:
                if not str(error).startswith("ambiguous declaration"):
                    raise
            else:
                raise ValueError("Ambiguous compiled-name control was accepted")
            try:
                resolve_reference(reference, entries, {"Airbender.MissingReferenceContext"})
            except ValueError as error:
                if not str(error).startswith("missing declaration"):
                    raise
            else:
                raise ValueError("Wrong-module reference control was accepted")
            try:
                resolve_reference("Airbender.ReferenceThatDoesNotExist", set(), {first[0]})
            except ValueError as error:
                if not str(error).startswith("missing declaration"):
                    raise
            else:
                raise ValueError("Missing compiled-name control was accepted")
            return
    raise ValueError("No compiled two-module ambiguity fixture was inventoried")


def check_links():
    count = 0
    for guide in GUIDES:
        for target in re.findall(r"\[[^]\n]*\]\(([^)\n]+)\)", guide.read_text()):
            link = urlsplit(target.strip("<>"))
            if link.scheme:
                continue
            path = (guide.parent / unquote(link.path)).resolve() if link.path else guide
            if not path.is_file():
                raise ValueError(f"{guide.relative_to(ROOT)}: missing link target {target}")
            if link.fragment:
                anchors = set()
                for heading in re.findall(r"^#+\s+(.+)$", path.read_text(), re.M):
                    slug = re.sub(r"[^\w\s-]", "", heading.strip().lower()).replace(" ", "-")
                    base, suffix = slug, 0
                    while slug in anchors:
                        suffix += 1
                        slug = f"{base}-{suffix}"
                    anchors.add(slug)
                if unquote(link.fragment) not in anchors:
                    raise ValueError(f"{guide.relative_to(ROOT)}: missing heading {target}")
            count += 1
    return count


def inventory(modules, references):
    imports = ["Airbender.Checks.Axioms", *modules, "Lean"]
    names = ", ".join('"' + name + '"' for name in sorted(references))
    code = "\n".join("import " + module for module in imports) + f'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut refs : Std.HashMap String (List String) := {{}}
  for ref in ([{names}] : List String) do
    let last := (ref.splitOn ".").getLast!
    refs := refs.insert last (ref :: refs[last]?.getD [])
  for (name, info) in env.constants.toList do
    if !isPrivateName name then
      if let .str _ last := name then
        for ref in refs[last]?.getD [] do
          if name.toString == ref || name.toString.endsWith ("." ++ ref) then
            if let some idx := env.getModuleIdxFor? name then
              let mod := env.header.moduleNames[idx]!
              logInfo m!"DOC_DECL {{ref}} {{name}} {{mod}}"
      if let .thmInfo _ := info then
        if let some idx := env.getModuleIdxFor? name then
          let mod := env.header.moduleNames[idx]!
          if mod.toString.startsWith "Airbender.Review." then
            if let some ranges ← findDeclarationRanges? name then
              let start := ranges.range.pos
              let finish := ranges.selectionRange.endPos
              logInfo m!"REVIEW_THEOREM {{mod}} {{name}} {{start.line}} {{start.column}} {{finish.line}} {{finish.column}}"
'''
    with tempfile.TemporaryDirectory(prefix="airbender-review-") as directory:
        path = Path(directory) / "Inventory.lean"
        path.write_text(code)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(result.stdout[-4000:])
    return result.stdout


def check_theorems(output, audit):
    declarations = set()
    pattern = r"^REVIEW_THEOREM (\S+) (\S+) (\d+) (\d+) (\d+) (\d+)$"
    for module, name, first, start, last, finish in re.findall(pattern, output, re.M):
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        lines = path.read_text().splitlines()[int(first) - 1:int(last)]
        lines[-1] = lines[-1][:int(finish)]
        lines[0] = lines[0][int(start):]
        header = re.sub(r"/-.*?-/|--[^\n]*", "", "\n".join(lines), flags=re.S)
        declared = re.search(r"\b(?:theorem|lemma)\s+([\w'.]+)\s*$", header)
        if declared and name.endswith("." + declared[1]):
            declarations.add(name)
    if not declarations:
        raise ValueError("No source-declared public Review theorems found")
    roots = re.findall(r"^#print axioms (\S+)\s*$", audit.read_text(), re.M)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate axiom audit roots")
    missing = declarations - set(roots)
    if missing:
        raise ValueError("Missing public theorem audit roots:\n" + "\n".join(sorted(missing)))
    return len(declarations)


def check_layers():
    graph = {".".join(path.relative_to(ROOT).with_suffix("").parts):
             re.findall(r"^import (\S+)$", path.read_text(), re.M)
             for path in (ROOT / "Airbender").rglob("*.lean")}
    if (ROOT / "Airbender.lean").is_file():
        graph["Airbender"] = re.findall(r"^import (\S+)$", (ROOT / "Airbender.lean").read_text(), re.M)
    # These existing proof assemblies reuse pooled retirement lemmas. Their
    # circuit models and statements do not require a whole-execution contract.
    assemblies = {f"Airbender.Review.Circuits.{family}.Theorems"
                  for family in ("JumpBranchSlt", "MulDiv", "ShiftBinop")}
    coupled = set()
    for module, dependencies in graph.items():
        for dependency in dependencies:
            if dependency.startswith("Airbender.Review.") and dependency not in graph:
                raise ValueError(f"Missing review module: {module} → {dependency}")
        if not module.startswith(("Airbender.Review.Helpers.", "Airbender.Review.Circuits.")):
            continue
        pending, seen = deque([[module]]), set()
        while pending:
            path = pending.popleft()
            current = path[-1]
            if current in seen:
                continue
            seen.add(current)
            if current.startswith("Airbender.Review.Trace."):
                if module in assemblies and path[1].startswith("Airbender.Proofs."):
                    coupled.add(module)
                    break
                raise ValueError("Whole-execution dependency in circuit context: " + " → ".join(path))
            pending.extend(path + [dependency] for dependency in graph.get(current, []))
    return len(coupled)


def verify_freshness_batches(snapshot, modules, checked):
    """Validate real aggregate receipts; no member is assigned fabricated metrics."""
    freshness = snapshot['freshness']
    workers = freshness['workers_limit']
    if (freshness['kind'] != 'normal_lake_no_build_query' or isinstance(workers, bool)
            or workers not in (1, 2, 3, 4)):
        raise ValueError('Invalid final freshness policy')
    targets = ['+' + module + ':olean' for module in modules]
    if (freshness['targets'] != targets or freshness['target_count'] != len(targets)
            or freshness['chunk_limit'] != 128 or set(freshness['modules']) != set(modules)):
        raise ValueError('Incomplete final freshness module coverage')
    batches = freshness['batches']
    if not isinstance(batches, list) or not batches:
        raise ValueError('Missing final freshness batch receipts')
    seen_batches, observed_targets, observed_modules = set(), [], {}

    def read(record):
        return json.loads(checked(record).read_text())

    def finite(value):
        return (not isinstance(value, bool) and isinstance(value, (int, float))
                and math.isfinite(value) and value >= 0)

    def values(text):
        result = []
        for line in text.splitlines():
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, (list, str)) or value is None:
                result.append(value)
        return result

    for batch in batches:
        label = batch['label']
        if (not isinstance(label, str) or not re.fullmatch(r'[A-Za-z0-9_.-]{1,160}', label)
                or label in seen_batches):
            raise ValueError('Invalid or duplicate freshness batch label')
        seen_batches.add(label)
        command, result = read(batch['guard_command']), read(batch['guard_result'])
        manifest_path = checked(batch['pool_manifest'])
        pool_path = checked(batch['pool_result'])
        if pool_path.name != 'result.json':
            raise ValueError('Invalid batch pool result path: ' + label)
        manifest = json.loads(manifest_path.read_text())
        pool = json.loads(pool_path.read_text())
        guard_output = checked(batch['guard_log']).read_text()
        aggregate_log = checked(batch['aggregate_log'])
        argv = command['command']
        if not argv or not Path(argv[0]).name.startswith('python'):
            raise ValueError('Invalid batch guard command: ' + label)
        expected = [argv[0], '-m', 'scripts.compilation_pool.guard', '--mib', '2560',
                    '--resident-mib', '5120', '--seconds', '900', '--lean-workers', str(workers),
                    '--log', str(aggregate_log), '--', argv[0], '-m', 'scripts.compilation_pool.pool',
                    '--manifest', str(manifest_path), '--output', str(pool_path.parent),
                    '--workers', str(workers)]
        if (argv != expected or command['cwd'] != str(ROOT) or result['command'] != argv
                or result['stage'] != label or isinstance(result['returncode'], bool) or result['returncode'] != 0
                or result['log'] != str(aggregate_log)):
            raise ValueError('Invalid batch guard command: ' + label)
        metrics = []
        for line in guard_output.splitlines():
            try:
                metric = json.loads(line)
            except ValueError:
                continue
            if isinstance(metric, dict) and 'reason' in metric:
                metrics.append(metric)
        if (len(metrics) != 1 or result['metrics'] != metrics or
                metrics[0].get('reason') != 'finished' or isinstance(metrics[0].get('exit'), bool) or metrics[0].get('exit') != 0 or
                metrics[0].get('live_owned_after') != [] or metrics[0].get('log') != result['log']):
            raise ValueError('Batch guard did not finish and reap its children: ' + label)
        metric = metrics[0]
        if (isinstance(metric.get('lean_workers_limit'), bool) or metric.get('lean_workers_limit') != workers or
                isinstance(metric.get('lean_workers_peak'), bool) or
                not isinstance(metric.get('lean_workers_peak'), int) or
                not 0 <= metric['lean_workers_peak'] <= workers or
                any(not finite(metric.get(key)) or metric[key] > maximum for key, maximum in
                    [('footprint_peak_mib', 2560), ('resident_peak_mib', 5120), ('seconds', 900)])):
            raise ValueError('Batch aggregate limits were not established: ' + label)
        if (pool.get('passed') is not True or pool.get('workers_limit') != workers or
                pool.get('manifest_sha256') != batch['pool_manifest']['sha256'] or
                not finite(pool.get('seconds')) or pool['seconds'] > 900):
            raise ValueError('Batch pool did not complete: ' + label)
        # Optional pool input identities must come from this actual frozen snapshot.
        for filename, digest in manifest.get('inputs', {}).items():
            if snapshot['inputs'].get(filename) != digest:
                raise ValueError('Batch pool input is not snapshot-bound: ' + filename)
        members, jobs, completed = batch['members'], manifest['jobs'], pool['jobs']
        if (not members or len(members) != len(jobs) or len(members) != len(completed)
                or batch['member_count'] != len(members)
                or batch['target_count'] != sum(len(member['targets']) for member in members)):
            raise ValueError('Incomplete batch member coverage: ' + label)
        by_label = {job['label']: job for job in completed}
        if len(by_label) != len(completed) or {job['label'] for job in jobs} != set(by_label):
            raise ValueError('Duplicate or missing pool members: ' + label)
        member_labels, intervals = set(), []
        for index, member in enumerate(members):
            member_label, selected = member['label'], member['targets']
            if (not isinstance(member_label, str) or
                    not re.fullmatch(r'[A-Za-z0-9_.-]{1,160}', member_label) or
                    member_label in member_labels or isinstance(member['pool_job_index'], bool) or
                    not isinstance(member['pool_job_index'], int) or
                    not 0 <= member['pool_job_index'] < len(completed) or
                    not isinstance(selected, list) or not 1 <= len(selected) <= 128):
                raise ValueError('Invalid final freshness member: ' + label)
            member_labels.add(member_label)
            job, actual = jobs[index], completed[member['pool_job_index']]
            if actual['label'] != member_label:
                raise ValueError('Wrong batch completion index: ' + member_label)
            native_command = ['lake', '--no-cache', '--no-build', '--json', 'query', *selected]
            expected_job = {'label': member_label, 'argv': native_command, 'cwd': str(ROOT),
                            'seconds': 900, 'dependencies': [], 'reserved_footprint_mib': 256,
                            'reserved_resident_mib': 1024, 'exclusive': False, 'allowed_exits': [0, 3]}
            if job != expected_job or actual is None or actual['argv'] != native_command or actual['cwd'] != str(ROOT):
                raise ValueError('Invalid read-only Lake member command: ' + member_label)
            if isinstance(actual.get('exit'), bool) or actual.get('exit') != 0:
                raise ValueError('Batch member failed: ' + member_label)
            begin, seconds = actual['started_monotonic'], actual['seconds']
            if not finite(begin) or not finite(seconds) or seconds > 900:
                raise ValueError('Invalid batch member timing: ' + member_label)
            intervals.append((begin, seconds))
            log = checked(member['log'])
            if log != pool_path.parent / (member_label + '.log') or actual['log'] != str(log):
                raise ValueError('Wrong batch member log: ' + member_label)
            parsed = values(log.read_text())
            if parsed != member['values'] or len(parsed) != len(selected):
                raise ValueError('Batch member JSON result count/content changed: ' + member_label)
            for target_index, (target, value) in enumerate(zip(selected, parsed)):
                if not isinstance(target, str) or target not in targets or not isinstance(value, str):
                    raise ValueError('Unexpected final freshness target/output: ' + member_label)
                module = target[1:-len(':olean')]
                expected_path = ROOT / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
                if (ROOT / value).resolve() != expected_path:
                    raise ValueError('Freshness query returned another compiled module: ' + module)
                if module in observed_modules:
                    raise ValueError('Duplicate final freshness target: ' + module)
                observed_modules[module] = {'batch': label, 'member': member_label,
                                            'target_index': target_index}
            observed_targets.extend(selected)
        # Pool durations are rounded to milliseconds. Bound overlap on both sides
        # of that rounding interval instead of inventing exact per-job resource data.
        def overlap(rounding):
            events = [(start, 1) for start, _ in intervals]
            events += [(max(start, start + duration + rounding), -1)
                       for start, duration in intervals]
            active = peak = 0
            for _, change in sorted(events, key=lambda event: (event[0], event[1])):
                active += change
                peak = max(peak, active)
            return max(1, peak)
        peak = pool['concurrent_jobs_peak']
        if (isinstance(peak, bool) or not isinstance(peak, int) or not 1 <= peak <= workers
                or not overlap(-.000501) <= peak <= overlap(.000501)):
            raise ValueError('Batch concurrency metadata is inconsistent: ' + label)
    if observed_targets != targets or observed_modules != freshness['modules']:
        raise ValueError('Incomplete final freshness module coverage')


def verify_build_snapshot(path):
    """Require current normal Lake freshness and unchanged actual inputs.

    V1 records completed serial builds. V2 records complete read-only Lake
    freshness queries after any exclusive normal repairs. Both validate actual
    receipts; neither supplies a replacement cache or a broad-build fallback.
    """
    def digest(path):
        with Path(path).open('rb') as stream:
            return hashlib.file_digest(stream, 'sha256').hexdigest()

    def checked(record, optional=False):
        target = Path(record['path'])
        if not target.is_absolute():
            raise ValueError('Build snapshot contains a relative path')
        expected = record['sha256']
        if expected is None and optional:
            if target.exists():
                raise ValueError('Previously absent compiled part now exists: ' + str(target))
        elif not isinstance(expected, str) or not target.is_file() or digest(target) != expected:
            raise ValueError('Build snapshot identity changed: ' + str(target))
        return target.resolve()

    snapshot = json.loads(Path(path).read_text())
    schema = snapshot.get('schema')
    if (schema not in {'airbender-serial-build-v1', 'airbender-serial-build-v2'} or
            snapshot.get('root') != str(ROOT) or snapshot.get('complete_project') is not True):
        raise ValueError('Require a complete serial build snapshot for this Lean root')
    sources = {'Airbender': ROOT / 'Airbender.lean'}
    for directory, base in [('Airbender', ROOT), ('Tests', ROOT),
                            ('generated/sail-rv32', ROOT / 'generated/sail-rv32')]:
        for source in (ROOT / directory).rglob('*.lean'):
            module = '.'.join(source.relative_to(base).with_suffix('').parts)
            if module in sources:
                raise ValueError('Duplicate current project module: ' + module)
            sources[module] = source.resolve()
    fields = ('sources', 'objects', 'imports') + (('jobs',) if schema == 'airbender-serial-build-v1' else ())
    for field in fields:
        if set(snapshot[field]) != set(sources):
            raise ValueError('Incomplete current project ' + field + ' inventory')
    inputs = snapshot['inputs']
    # Derive required identities from this checkout, independently of receipt keys.
    required = set(sources.values()) | {ROOT / name for name in (
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'scripts/axiom_baseline.json', 'artifacts/setup/native-cargo.lock',
        'generated/sail-rv32/provenance.json')}
    for pattern in ('scripts/*.py', 'scripts/*.lean', 'scripts/fixtures/*.lean.in',
                    'artifacts/setup/*.json', '.lake/packages/*/lakefile.toml',
                    '.lake/packages/*/lakefile.lean', '.lake/packages/*/lean-toolchain'):
        required.update(ROOT.glob(pattern))
    for suffix in ('.py', '.lean', '.in', '.json'):
        required.update(target for target in (ROOT / 'scripts').rglob('*' + suffix) if target.is_file())
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    required.update(ROOT / item['path'] for item in config.get('input_file', []))
    repo = ROOT.parent.parent
    native = json.loads((ROOT / 'artifacts/setup/manifest.json').read_text())
    evidence = json.loads((ROOT / 'artifacts/setup/native-evidence.json').read_text())
    sail = json.loads((ROOT / 'generated/sail-rv32/provenance.json').read_text())
    required.update(repo / name for name in native['source_sha256'])
    required.update(repo / name for name in evidence['sources'])
    required.update(repo / name for name in sail['platform_parameterization']['airbender_evidence_sha256'])
    missing = {str(target.resolve()) for target in required} - set(inputs)
    if missing:
        raise ValueError('Missing required build inputs: ' + ', '.join(sorted(missing)[:8]))
    for name, expected in inputs.items():
        checked({'path': name, 'sha256': expected})
    for name in ('check_review.py', 'check_lean.py'):
        target = ROOT / 'scripts' / name
        if inputs.get(str(target)) != digest(target):
            raise ValueError('Checker input missing from verified build: ' + name)
    guard = checked(snapshot['guard'])
    if checked(snapshot['checker']) != ROOT / 'scripts/check_lean.py':
        raise ValueError('Wrong serial build frontend identity')
    if inputs.get(str(guard)) != snapshot['guard']['sha256']:
        raise ValueError('Guard absent from verified inputs')
    queue_path = checked({'path': snapshot['source_queue'], 'sha256': snapshot['source_queue_sha256']})
    queue = json.loads(queue_path.read_text())
    modules = queue['modules']
    if (queue.get('scope') != 'complete_project' or len(modules) != len(set(modules)) or
            set(modules) != set(sources) or queue['imports'] != snapshot['imports'] or
            queue['sources'] != {name: str(source) for name, source in sources.items()}):
        raise ValueError('Incomplete or inconsistent normal source queue')
    position = {name: index for index, name in enumerate(modules)}
    if schema == 'airbender-serial-build-v2':
        if 'jobs' in snapshot:
            raise ValueError('Batch snapshot must not synthesize per-module jobs')
        verify_freshness_batches(snapshot, modules, checked)
    external = set()
    for module, source in sources.items():
        if checked(snapshot['sources'][module]) != source or inputs.get(str(source)) != snapshot['sources'][module]['sha256']:
            raise ValueError('Source not covered by successful build: ' + module)
        for dependency in snapshot['imports'][module]:
            if dependency in sources:
                if position[dependency] >= position[module]:
                    raise ValueError('Dependency was not checked before consumer: ' + module)
            else:
                external.add(dependency)
        parts = snapshot['objects'][module]
        if set(parts) != {'', '.server', '.private'}:
            raise ValueError('Incomplete compiled part inventory: ' + module)
        base = ROOT / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        for suffix, record in parts.items():
            if checked(record, optional=bool(suffix)) != Path(str(base) + suffix):
                raise ValueError('Wrong compiled object path: ' + module)
        if schema == 'airbender-serial-build-v1':
            receipt = snapshot['jobs'][module]
            records = {}
            for kind in ('command', 'result', 'log'):
                file = checked({'path': receipt[kind], 'sha256': receipt[kind + '_sha256']})
                if kind != 'log':
                    records[kind] = json.loads(file.read_text())
            command = records['command']['command']
            expected = [str(guard), '--mib', '2560', '--resident-mib', '5120', '--seconds', '900',
                        '--log', receipt['log'], '--', 'lake', '--no-cache', 'build', '+' + module + ':olean']
            result = records['result']
            if (len(command) != len(expected) + 1 or command[1:] != expected or
                    not Path(command[0]).name.startswith('python') or records['command']['cwd'] != str(ROOT) or
                    result['command'] != command or result['stage'] != 'source-' + module or
                    result['returncode'] != 0 or result['log'] != receipt['log']):
                raise ValueError('Receipt is not the required normal bounded source build: ' + module)
            metrics = result['metrics']
            if (len(metrics) != 1 or metrics[0].get('reason') != 'finished' or
                    metrics[0].get('exit') != 0 or metrics[0].get('live_owned_after') != [] or
                    metrics[0].get('log') != receipt['log']):
                raise ValueError('Source build did not finish and reap its children: ' + module)
    if (snapshot['external_imports_scope'] != 'direct_workspace_imports_of_project_modules' or
            snapshot['external_freshness_basis'] != (
                'normal Lake dependencies of every successful project olean target'
                if schema == 'airbender-serial-build-v1' else
                'normal Lake --no-build dependency freshness of every final project olean query') or
            set(snapshot['external_imports']) != external or set(snapshot['external_sources']) != external):
        raise ValueError('Incomplete explicit external dependency inventory')
    libraries = [ROOT / '.lake/build/lib/lean',
                 *sorted((ROOT / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    for module in external:
        relative = Path(*module.split('.'))
        bases = {library.resolve() for library in libraries
                 if (library / relative.with_suffix('.olean')).is_file()}
        if len(bases) != 1:
            raise ValueError('Missing or ambiguous actual external module: ' + module)
        library = bases.pop()
        # These pinned package sources use their module path under the package
        # root. Fail on a changed source layout rather than accepting a redirect.
        source = library.parents[3] / relative.with_suffix('.lean')
        if checked(snapshot['external_sources'][module]) != source:
            raise ValueError('Wrong external source module path: ' + module)
        parts = snapshot['external_imports'][module]
        if set(parts) != {'', '.server', '.private'}:
            raise ValueError('Incomplete external compiled parts: ' + module)
        base = library / relative.with_suffix('.olean')
        for suffix, record in parts.items():
            if checked(record, optional=bool(suffix)) != Path(str(base) + suffix):
                raise ValueError('Wrong external compiled module path: ' + module)
    return len(sources)


def check_snapshot_controls(path):
    """Mutate only copies of real completed receipts, never production objects."""
    original = json.loads(Path(path).read_text())
    passed = []
    with tempfile.TemporaryDirectory(prefix='airbender-review-controls-') as directory:
        temporary = Path(directory).resolve()

        def rejected(label, alter, prefix):
            specimen = json.loads(json.dumps(original))
            alter(specimen)
            target = temporary / (label + '.snapshot.json')
            target.write_text(json.dumps(specimen))
            try:
                verify_build_snapshot(target)
            except ValueError as error:
                if not str(error).startswith(prefix):
                    raise ValueError(f'{label} failed for an unintended reason: {error}') from error
            else:
                raise ValueError('Invalid build snapshot accepted: ' + label)
            passed.append(label)

        def missing_config(specimen):
            del specimen['inputs'][str(ROOT / 'lake-manifest.json')]
        rejected('missing-required-configuration', missing_config, 'Missing required build inputs:')

        dependency = next(name for deps in original['imports'].values() for name in deps
                          if name in original['sources'])
        def missing_dependency(specimen):
            fields = ('sources', 'objects', 'imports')
            if original['schema'] == 'airbender-serial-build-v1':
                fields += ('jobs',)
            for field in fields:
                del specimen[field][dependency]
        rejected('missing-project-dependency', missing_dependency, 'Incomplete current project')

        module = next(iter(original['sources']))
        def stale_object(specimen):
            specimen['objects'][module]['']['sha256'] = '0' * 64
        rejected('stale-public-object', stale_object, 'Build snapshot identity changed:')

        if original['schema'] == 'airbender-serial-build-v1':
            def rewrite_job(specimen, label, command_change=None, metric_change=None):
                receipt = specimen['jobs'][module]
                command = json.loads(Path(receipt['command']).read_text())
                result = json.loads(Path(receipt['result']).read_text())
                if command_change:
                    command_change(command['command'])
                    result['command'] = command['command']
                if metric_change:
                    metric_change(result['metrics'][0])
                for kind, value in [('command', command), ('result', result)]:
                    target = temporary / (label + '.' + kind + '.json')
                    target.write_text(json.dumps(value))
                    receipt[kind] = str(target)
                    receipt[kind + '_sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()

            def wrong_cap(specimen):
                def alter(command):
                    command[command.index('--mib') + 1] = '2561'
                rewrite_job(specimen, 'raised-cap', command_change=alter)
            rejected('raised-cap-with-consistent-metadata-hashes', wrong_cap,
                     'Receipt is not the required normal bounded source build:')

            def unreaped(specimen):
                rewrite_job(specimen, 'unreaped', metric_change=lambda metric:
                            metric.update(live_owned_after=[1]))
            rejected('unreaped-with-consistent-metadata-hashes', unreaped,
                     'Source build did not finish and reap its children:')

        else:
            def rewrite_batch(specimen, label, command_change=None, metric_change=None, pool_change=None):
                receipt = specimen['freshness']['batches'][0]
                command = json.loads(Path(receipt['guard_command']['path']).read_text())
                result = json.loads(Path(receipt['guard_result']['path']).read_text())

                def replace(kind, value, text=False):
                    if kind == 'pool_result':
                        folder = temporary / label
                        folder.mkdir(exist_ok=True)
                        target = folder / 'result.json'
                    else:
                        target = temporary / (label + '.' + kind + ('.log' if text else '.json'))
                    target.write_text(value if text else json.dumps(value))
                    receipt[kind] = {'path': str(target),
                                     'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}
                    return target

                if command_change:
                    command_change(command['command'])
                if pool_change:
                    pool = json.loads(Path(receipt['pool_result']['path']).read_text())
                    # Keep every output path consistent in this isolated copy.
                    # macOS may spell the temporary root through /var or /private/var.
                    folder = temporary / label
                    folder.mkdir()
                    for job in pool['jobs']:
                        target = folder / (job['label'] + '.log')
                        target.write_bytes(Path(job['log']).read_bytes())
                        job['log'] = str(target)
                    for member in receipt['members']:
                        target = folder / (member['label'] + '.log')
                        member['log'] = {'path': str(target),
                                         'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}
                    first = receipt['members'][0]['label']
                    pool_change(next(job for job in pool['jobs'] if job['label'] == first))
                    target = replace('pool_result', pool)
                    command['command'][command['command'].index('--output') + 1] = str(target.parent.resolve())
                result['command'] = command['command']
                if metric_change:
                    metric_change(result['metrics'][0])
                    replace('guard_log', json.dumps(result['metrics'][0]) + '\n', text=True)
                replace('guard_command', command)
                replace('guard_result', result)

            def wrong_batch_cap(specimen):
                def alter(command):
                    command[command.index('--mib') + 1] = '2561'
                rewrite_batch(specimen, 'raised-batch-cap', command_change=alter)
            rejected('raised-cap-with-consistent-batch-metadata-hashes', wrong_batch_cap,
                     'Invalid batch guard command:')

            def unreaped_batch(specimen):
                rewrite_batch(specimen, 'unreaped-batch', metric_change=lambda metric:
                              metric.update(live_owned_after=[1]))
            rejected('unreaped-with-consistent-batch-metadata-hashes', unreaped_batch,
                     'Batch guard did not finish and reap its children:')

            def failed_member(specimen):
                rewrite_batch(specimen, 'failed-member', pool_change=lambda job: job.update(exit=1))
            rejected('failed-member-with-consistent-pool-metadata-hashes', failed_member,
                     'Batch member failed:')

            def missing_freshness(specimen):
                del specimen['freshness']['modules'][module]
            rejected('missing-final-freshness-coverage', missing_freshness,
                     'Incomplete final freshness module coverage')

        optional = next(((field, name, suffix)
                         for field in ('objects', 'external_imports')
                         for name, parts in original[field].items()
                         for suffix in ('.server', '.private')
                         if parts[suffix]['sha256'] is not None), None)
        if optional is not None:
            def false_absence(specimen):
                specimen[optional[0]][optional[1]][optional[2]]['sha256'] = None
            rejected('false-optional-part-absence', false_absence,
                     'Previously absent compiled part now exists:')
        else:
            # Legacy non-module sources legitimately have no optional parts.
            # Exercise the opposite identity mismatch against an actual absence.
            absent = next((name, suffix) for name, parts in original['objects'].items()
                          for suffix in ('.server', '.private')
                          if parts[suffix]['sha256'] is None)
            def false_presence(specimen):
                specimen['objects'][absent[0]][absent[1]]['sha256'] = '0' * 64
            rejected('false-optional-part-presence', false_presence,
                     'Build snapshot identity changed:')

        external = sorted(original['external_imports'])
        if len(external) < 2:
            raise ValueError('Need two actual external modules for redirect control')
        def redirect(specimen):
            specimen['external_imports'][external[0]] = specimen['external_imports'][external[1]]
        rejected('external-module-redirect-with-valid-file-hashes', redirect,
                 'Wrong external compiled module path:')
    return len(passed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verified-build', type=Path, required=True,
                        help='Complete unchanged snapshot from scripts/check_lean.py')
    args = parser.parse_args()
    guide_hashes = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in GUIDES}
    compiled = verify_build_snapshot(args.verified_build)
    snapshot_controls = check_snapshot_controls(args.verified_build)
    from check_setup_artifacts import check as check_setup_artifacts
    from check_native_evidence import check as check_native_evidence
    from check_sail_reference import check as check_sail_reference
    artifacts, sources, circuits = check_setup_artifacts()
    native = check_native_evidence()
    sail = check_sail_reference()
    print(f"PASS {compiled} normally validated source targets retain their exact inputs and outputs")
    print(f"PASS {snapshot_controls} actual build-snapshot mutation controls")
    print(f"PASS {artifacts} setup artifacts, {sources} native source hashes, {circuits} production circuit identities plus derived decoder fixture")
    print(f"PASS native evidence: {native}; Sail reference: {sail}")
    modules = sorted({".".join(path.relative_to(ROOT).with_suffix("").parts)
                      for path in (ROOT / "Airbender/Review").rglob("*.lean")} |
                     set().union(*(guide_context(guide) for guide in GUIDES)))
    references = guide_names() | {"Word", "active"}
    output = inventory(modules, references)
    reference_count = check_references(output)
    count = check_theorems(output, ROOT / "Airbender/Checks/Axioms.lean")
    print(f"PASS {count} public Review theorems have explicit axiom audit roots")
    print(f"PASS {reference_count} contextual guide declarations; compiled ambiguity/missing controls")
    print(f"PASS {check_links()} local guide links and heading anchors resolve")
    print(f"PASS context/trace separation; {check_layers()} documented proof-assembly dependencies")
    if guide_hashes != {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in GUIDES}:
        raise ValueError('Guide contents changed during reference validation')


if __name__ == "__main__":
    try:
        main()
    except (KeyError, TypeError, OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL {error}") from error
