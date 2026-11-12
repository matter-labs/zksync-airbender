#!/usr/bin/env python3
"""Check spec boundaries with Lean's import parser and the full source closure."""
from collections import deque
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def load_graph(modules, source_root=None):
    command = ['lake', 'env', 'lean', '--run', 'scripts/ImportGraph.lean']
    if source_root is not None:
        command += ['--source-root', str(source_root)]
    command += modules
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=True)
    return dict(json.loads(result.stdout))


def check_graph(graph, roots):
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
            if forbidden:
                raise ValueError('Spec import boundary: ' + ' → '.join(path))
            if current not in graph:
                raise ValueError('Missing module in import graph: ' + current)
            pending.extend(path + [dependency] for dependency in graph[current])


def main():
    roots = sorted('.'.join(p.relative_to(ROOT / 'human').with_suffix('').parts)
                   for p in (ROOT / 'human').rglob('*.lean'))
    graph = load_graph(roots)
    check_graph(graph, roots)
    print(f'PASS import closure: {len(roots)} spec modules, {len(graph)} total modules')


if __name__ == '__main__':
    main()
