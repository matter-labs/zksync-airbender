#!/usr/bin/env python3
"""Check source procedures against the trust lists in the reviewed specification."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'human/Human/Trust.lean'
RESTRICTED = re.compile(r'\b(?:unsafe|partial|implemented_by|extern)\b')
FORBIDDEN = re.compile(r'\b(?:axiom|sorry|native_decide|bv_decide)\b')
RAW_STRING = re.compile(r'r(#+)"')


def source_text(text):
    """Remove nested Lean comments; return code with and without string literals.

    Restricted tokens in strings also need an allowed module, since tactic code
    can emit those strings as Lean code.
    """
    visible, code = [], []
    index = 0
    while index < len(text):
        if text.startswith('--', index):
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
            continue
        if text.startswith('/-', index):
            depth = 1
            index += 2
            while index < len(text) and depth:
                if text.startswith('/-', index):
                    depth += 1
                    index += 2
                elif text.startswith('-/', index):
                    depth -= 1
                    index += 2
                else:
                    if text[index] == '\n':
                        visible.append('\n')
                        code.append('\n')
                    index += 1
            if depth:
                raise ValueError('Unclosed Lean comment')
            continue
        raw = RAW_STRING.match(text, index) if text[index] == 'r' else None
        if raw:
            end = text.find('"' + raw[1], index + len(raw[0]))
            if end < 0:
                raise ValueError('Unclosed raw string')
            end += 1 + len(raw[1])
            visible.append(text[index:end])
            code.append(' ' + '\n' * text[index:end].count('\n'))
            index = end
            continue
        if text[index] == '"':
            start = index
            index += 1
            while index < len(text):
                if text[index] == '\\':
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            visible.append(text[start:index])
            code.append(' ' + '\n' * text[start:index].count('\n'))
            continue
        visible.append(text[index])
        code.append(text[index])
        index += 1
    return ''.join(visible), ''.join(code)


def manifest_list(name):
    text, _ = source_text(MANIFEST.read_text())
    match = re.search(r'\bdef ' + re.escape(name) + r' : List String := (\[[^]]*\])', text)
    if not match:
        raise ValueError('Trust list must be a literal List String: ' + name)
    values = json.loads(match[1])
    if not values or len(values) != len(set(values)) or any(
            not re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', value) for value in values):
        raise ValueError('Trust list is empty, duplicated or malformed: ' + name)
    return set(values)


def check_source(module, text, allowed):
    visible, code = source_text(text)
    if match := FORBIDDEN.search(code):
        raise ValueError(f'{module}: prohibited source token {match[0]}')
    found = set(RESTRICTED.findall(visible))
    if found and module not in allowed:
        raise ValueError(f'{module}: unlisted source procedures: {", ".join(sorted(found))}')
    return bool(found)


def main():
    roots = manifest_list('trustedModuleRoots')
    allowed = manifest_list('trustedTacticModules')
    modules, used = set(), set()
    for directory in ('human', 'proven', 'test'):
        for path in (ROOT / directory).rglob('*.lean'):
            module = '.'.join(path.relative_to(ROOT / directory).with_suffix('').parts)
            modules.add(module)
            if check_source(module, path.read_text(), allowed):
                used.add(module)
    if missing := allowed - modules:
        raise ValueError('Missing allowed modules: ' + ', '.join(sorted(missing)))
    if stale := allowed - used:
        raise ValueError('Unused procedure permissions: ' + ', '.join(sorted(stale)))
    print(f'PASS {len(modules)} source modules: {len(roots)} external roots and {len(allowed)} procedure modules')


if __name__ == '__main__':
    main()
