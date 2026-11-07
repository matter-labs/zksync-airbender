#!/usr/bin/env python3
"""Generate cached verification sources and check their freshness.

Family modules supply the individual source generators. This entry point
never runs Lean, replay, controls or builds for source commands.
The compiler subcommand explicitly invokes the Rust capture producer.
"""
import argparse
from pathlib import Path
import re
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parent
LEAN = SCRIPTS.parent


def airbender_imports(text):
    """Read import commands outside strings and nested Lean comments."""
    token = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\])*"', re.S)
    delimiter = re.compile(r'/-|-/')
    pieces, position = [], 0
    while match := token.search(text, position):
        first, last = match.span()
        if match.group() == '/-':
            depth = 1
            while depth:
                boundary = delimiter.search(text, last)
                if boundary is None:
                    raise ValueError('Unclosed Lean block comment')
                depth += 1 if boundary.group() == '/-' else -1
                last = boundary.end()
        pieces.append(text[position:first])
        pieces.append(re.sub(r'[^\n]', ' ', text[first:last]))
        position = last
    pieces.append(text[position:])
    code = ''.join(pieces)
    command = re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import(?:[ \t]+all)?[ \t\r\n]+([^\n]+)')
    module = re.compile(r"(?<![\w.])Airbender(?:\.(?:«[^»]+»|[^\W\d][\w']*))*(?![\w.])")
    for header in command.finditer(code):
        for imported in module.finditer(header[1]):
            line = code.count('\n', 0, header.start(1) + imported.start()) + 1
            parts = [quoted or plain for quoted, plain in
                     re.findall(r'«([^»]+)»|([^ .\t]+)', imported.group())]
            yield imported.group(), parts, line


def check_tracked_imports(repo=LEAN.parents[1]):
    """Require every tracked Lean Airbender import to have a tracked source."""
    names = subprocess.check_output(['git', 'ls-files', '-z', '--', '*.lean'],
                                    cwd=repo, text=True).split('\0')
    tracked = {name for name in names if name and (repo / name).is_file()}
    prefix = LEAN.relative_to(repo).as_posix()
    missing, count = [], 0
    for name in sorted(tracked):
        for module, parts, line in airbender_imports((repo / name).read_text()):
            count += 1
            target = prefix + '/' + '/'.join(parts) + '.lean'
            if target not in tracked:
                missing.append(f'{name}:{line}: {module} -> {target}')
    if missing:
        raise ValueError('Unresolved tracked Airbender imports:\n' + '\n'.join(missing))
    print(f'PASS {count} Airbender imports in {len(tracked)} tracked Lean files', flush=True)

# Preserve dependency order from the established generated-source gate.
GENERATORS = (
    ('tables', 'gkr_packed_fixed_captures.py', ()),
    ('tables', 'gkr_unified_equal_chunks.py', ()),
    ('tables', 'gkr_unified_prefix_assembly.py', ('--stage', 'column')),
    ('captures', 'gkr_full_arithmetic_certificate.py', ()),
    ('captures', 'gkr_numeric_arithmetic.py', ()),
    ('captures', 'gkr_clean_ideal.py', ()),
    ('captures', 'gkr_packed_wiring.py', ()),
    ('tables', 'generate_packed_xor9.py', ()),
    ('tables', 'generate_packed_chi.py', ()),
    ('tables', 'generate_shift_packed_encoding.py', ()),
    ('tables', 'generate_shift_packed_reference.py', ()),
    ('tables', 'generate_shift_output_certificates.py', ()),
    ('tables', 'generate_shift_bitwise.py', ()),
    ('captures', 'generate_native_lookup_requests.py', ()),
    ('tables', 'gkr_shift_prefix_instances.py', ()),
    ('tables', 'gkr_shift_prefix_assembly.py', ()),
    ('tables', 'gkr_packed_rotate_boundary.py', ()),
    ('tables', 'gkr_unified_prefix.py', ('--unit', '14')),
    ('tables', 'gkr_packed_column1_spans.py', ()),
    ('tables', 'gkr_unified_prefix.py', ()),
    ('tables', 'gkr_unified_prefix.py', ('--assembly',)),
    ('tables', 'generate_shift_extent_checks.py', ()),
    ('tables', 'generate_shift_metadata.py', ()),
    ('tables', 'gkr_packed_region_lengths.py', ()),
    ('tables', 'generate_array_samples.py', ()),
    ('tables', 'generate_aligned_samples.py', ()),
    ('captures', 'gkr_packed_memory_frame.py', ()),
    ('captures', 'gkr_memory_frame_instances.py', ()),
    ('captures', 'gkr_packed_functional_steps.py', ()),
    ('captures', 'gkr_functional_instances.py', ()),
    ('captures', 'gkr_packed_functional_base.py', ()),
    ('captures', 'gkr_packed_counter_frame.py', ()),
    ('captures', 'gkr_packed_history_erasure.py', ()),
    ('captures', 'gkr_packed_clean_arguments.py', ()),
    ('captures', 'gkr_packed_lookup_source.py', ()),
    ('captures', 'gkr_packed_source_freshness.py', ()),
    ('captures', 'gkr_table_instances.py', ()),
    ('captures', 'gkr_packed_worker_ports.py', ()),
    ('captures', 'gkr_worker_ports_instances.py', ()),
    ('captures', 'gkr_packed_helper_validity.py', ()),
    ('captures', 'gkr_helper_validity_instances.py', ()),
    ('captures', 'gkr_packed_helper_payload.py', ()),
    ('captures', 'gkr_helper_instances.py', ()),
    ('captures', 'gkr_packed_memory_payload.py', ()),
    ('captures', 'gkr_memory_certificate.py', ()),
    ('captures', 'gkr_packed_query_frame.py', ()),
    ('captures', 'gkr_query_frame_instances.py', ()),
    ('tables', 'generate_packed_xor7.py', ()),
    ('tables', 'gkr_unified_special_chunks.py', ()),
    ('tables', 'gkr_unified_chunk_lengths.py', ()),
    ('tables', 'gkr_unified_prefix_assembly.py', ()),
    ('captures', 'gkr_materialized_instances.py', ()),
)

WRITE_BY_DEFAULT = ('generate_native_lookup_requests.py', 'gkr_packed_helper_payload.py', 'gkr_packed_helper_validity.py', 'gkr_packed_memory_payload.py', 'gkr_packed_worker_ports.py', 'gkr_unified_chunk_lengths.py', 'gkr_unified_equal_chunks.py', 'gkr_unified_prefix.py', 'gkr_unified_prefix_assembly.py', 'gkr_unified_special_chunks.py', 'gkr_worker_ports_instances.py')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "all", "captures", "tables", "compiler"))
    parser.add_argument("--write", action="store_true", help="Write changed sources; source commands otherwise check freshness")
    parser.add_argument("--family", action="append", help="Limit the compiler export subcommand")
    parser.add_argument("--output", type=Path, help="Compiler export destination")
    args = parser.parse_args()
    if args.command == "check" and args.write:
        parser.error("check does not write generated sources")
    if args.command != "compiler" and (args.family or args.output):
        parser.error("--family and --output apply to compiler exports")
    if args.command == "compiler":
        command = [sys.executable, str(SCRIPTS / "export_gkr_translations.py")]
        for family in args.family or []:
            command += ["--family", family]
        if args.output:
            command += ["--output", str(args.output.resolve())]
        subprocess.run(command, cwd=LEAN, check=True)
        return
    if not args.write:
        check_tracked_imports()
    count = 0
    for group, script, options in GENERATORS:
        if args.command not in ("all", "check", group):
            continue
        command = [sys.executable, str(SCRIPTS / script), *options]
        command += ([] if script in WRITE_BY_DEFAULT else ["--write"]) if args.write else ["--check"]
        print(("GENERATE" if args.write else "FRESHNESS") + " " + script, flush=True)
        subprocess.run(command, cwd=LEAN, check=True)
        count += 1
    print(f"PASS {count} cached verification source generators", flush=True)

if __name__ == "__main__":
    main()
