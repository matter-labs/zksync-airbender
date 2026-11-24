#!/usr/bin/env python3
"""Check spec boundaries with Lean's import parser and the full source closure."""
from collections import deque
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SAIL_ROOTS = {'Sail', 'SailRV32'}


def load_graph(modules, source_root=None):
    command = ['lake', 'env', 'lean', '--run', 'scripts/ImportGraph.lean']
    if source_root is not None:
        command += ['--source-root', str(source_root)]
    command += modules
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=True)
    return dict(json.loads(result.stdout))


def check_graph(graph, roots, trusted=None, sail_modules=None):
    """Reject forbidden imports. With `sail_modules`, only those roots reach the Sail model, and each of them does."""
    reaches_sail = set()
    for root in roots:
        pending, seen = deque([[root]]), set()
        while pending:
            path = pending.popleft()
            current = path[-1]
            if current in seen:
                continue
            seen.add(current)
            forbidden = current.split('.')[0] in {'Proven', 'Tests', 'Checks'}
            forbidden |= root != 'CleanCore.Equivalence' and current.split('.')[0] == 'Clean'
            if trusted is not None:
                prefix = current.split('.')[0]
                forbidden |= prefix not in trusted | {'Human', 'CleanCore'} and not (
                    root == 'CleanCore.Equivalence' and prefix == 'Clean')
            if forbidden:
                raise ValueError('Spec import boundary: ' + ' → '.join(path))
            if current.split('.')[0] in SAIL_ROOTS:
                if sail_modules is not None and root not in sail_modules:
                    raise ValueError('Sail import boundary: ' + ' → '.join(path))
                reaches_sail.add(root)
            if current not in graph:
                raise ValueError('Missing module in import graph: ' + current)
            pending.extend(path + [dependency] for dependency in graph[current])
    if sail_modules is not None and (stale := set(sail_modules) - reaches_sail):
        raise ValueError('Listed Sail modules do not import the Sail model: ' + ', '.join(sorted(stale)))


def check_sail_edges(graph, listed):
    """The direct imports of the Sail model from our modules are exactly the listed edges."""
    edges = {(module, dependency) for module, dependencies in graph.items()
             if module.split('.')[0] in {'Human', 'Proven'}
             for dependency in dependencies if dependency.split('.')[0] in SAIL_ROOTS}
    if unlisted := edges - listed:
        raise ValueError('Unlisted direct Sail import: ' + ', '.join(f'{a} → {b}' for a, b in sorted(unlisted)))
    if stale := listed - edges:
        raise ValueError('Listed Sail import is absent: ' + ', '.join(f'{a} → {b}' for a, b in sorted(stale)))


# The definitions that the machine claims use. Their closure reads no raw setup data, except the BLAKE2 round and
# split Keccak tables, which are defined by their imported rows.
DEFINITION_ROOTS = ['Human.Compiler.NativeTargets']
TABLES_FROM_DATA = {
    'Human.Circuits.Blake2Round.SetupArtifact',
    'Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact',
    'Human.Circuits.KeccakSplit.ThetaRho.SetupArtifact',
    'Human.Circuits.KeccakSplit.Chi5.SetupArtifact',
}


def check_raw_data(graph, roots, data_modules, allowed):
    """Reject a path from a definition root to a setup data module outside `allowed`."""
    for root in roots:
        pending, seen = deque([[root]]), set()
        while pending:
            path = pending.popleft()
            current = path[-1]
            if current in seen:
                continue
            seen.add(current)
            if current in data_modules and current not in allowed:
                raise ValueError('Raw setup data in the definitions: ' + ' → '.join(path))
            pending.extend(path + [dependency] for dependency in graph.get(current, []))


# The setup import command name as a whole token. The syntax atom that declares the command and a name literal (after a
# backtick) do not run it. Every other occurrence counts, comments included, so the check fails closed.
SETUP_IMPORT_ATOM = '"import_setup_blocks "'
SETUP_IMPORT_TOKEN = re.compile(r"(?<![\w'`])import_setup_blocks(?![\w'!?])")


def runs_setup_import(text):
    """Whether a module text can run `import_setup_blocks`."""
    return SETUP_IMPORT_TOKEN.search(text.replace(SETUP_IMPORT_ATOM, ' ')) is not None


def module_path(module):
    return ROOT.joinpath('human', *module.split('.')).with_suffix('.lean')


def module_names(folder):
    return sorted('.'.join(p.relative_to(ROOT / folder).with_suffix('').parts) for p in (ROOT / folder).rglob('*.lean'))


def main():
    from check_trusted_code import manifest_list, manifest_edges
    roots = module_names('human')
    graph = load_graph(roots + module_names('proven'))
    check_graph(graph, roots, manifest_list('trustedModuleRoots'), manifest_list('sailModules'))
    listed = manifest_edges('sailImportEdges')
    check_sail_edges(graph, listed)
    data_modules = {name for name in roots if runs_setup_import(module_path(name).read_text())}
    check_raw_data(graph, DEFINITION_ROOTS, data_modules, TABLES_FROM_DATA)
    print(f'PASS import closure: {len(roots)} spec modules, {len(graph)} total modules, '
          f'{len(listed)} direct Sail imports, {len(data_modules)} setup data modules outside the definitions')


if __name__ == '__main__':
    main()
