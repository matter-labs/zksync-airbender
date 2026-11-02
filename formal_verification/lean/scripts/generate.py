#!/usr/bin/env python3
"""Generate cached verification sources and check their freshness.

Family modules remain implementation libraries during consolidation. This
entry point never runs Lean, replay, controls or builds for source commands.
The validate subcommand runs the final checker controls with per-command guards.
The compiler subcommand explicitly invokes the Rust capture producer.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

SCRIPTS = Path(__file__).resolve().parent
LEAN = SCRIPTS.parent

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

CONTROLS = (
    ('packed-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_*.py', '-v')),
    ('compiler-provenance-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_gkr_translation_provenance.py', '-v')),
    ('numeric-bindings', ('python3', 'scripts/check_numeric_arithmetic_controls.py')),
    ('packed-normalization', ('python3', 'scripts/check_packed_normalization_controls.py')),
    ('clean-placement', ('python3', 'scripts/check_clean_placement_controls.py')),
    ('clean-ideal', ('python3', 'scripts/check_clean_ideal_controls.py')),
    ('wiring-kernel-controls', ('python3', 'scripts/check_wiring_controls.py')),
    ('rotation-kernel-controls', ('python3', 'scripts/check_rotation_binding_controls.py')),
    ('setup-normalization-controls', ('python3', 'scripts/check_setup_normalization_controls.py')),
    ('setup-prefix-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_shift_prefix.py')),
    ('setup-span-controls', ('python3', 'scripts/check_setup_span_controls.py')),
    ('rotate-boundary-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_rotate_boundary.py')),
    ('fixed-column-one-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_column1_spans.py')),
    ('packed-length-controls', ('python3', 'scripts/check_packed_length_controls.py')),
    ('shift-extent-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_shift_extent_checks.py')),
    ('shift-metadata-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_shift_metadata.py')),
    ('shift-metadata-kernel-controls', ('python3', 'scripts/check_shift_metadata_controls.py')),
    ('natural-setup-kernel-controls', ('python3', 'scripts/check_natural_setup_controls.py')),
    ('setup-length-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_region_lengths.py')),
    ('setup-length-kernel-controls', ('python3', 'scripts/check_setup_length_controls.py')),
    ('array-sample-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_array_samples.py')),
    ('array-sample-kernel-controls', ('python3', 'scripts/check_array_sample_controls.py')),
    ('aligned-sample-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_aligned_samples.py')),
    ('aligned-sample-kernel-controls', ('python3', 'scripts/check_aligned_sample_controls.py')),
    ('numeric-memory-frame-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_memory_frame.py')),
    ('numeric-memory-frame-kernel-controls', ('python3', 'scripts/check_memory_frame_controls.py')),
    ('numeric-functional-step-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_functional_steps.py')),
    ('numeric-functional-step-kernel-controls', ('python3', 'scripts/check_functional_step_controls.py')),
    ('numeric-functional-base-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_functional_base.py')),
    ('numeric-functional-base-kernel-controls', ('python3', 'scripts/check_functional_base_controls.py')),
    ('numeric-counter-frame-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_counter_frame.py')),
    ('numeric-counter-frame-kernel-controls', ('python3', 'scripts/check_counter_frame_controls.py')),
    ('numeric-history-erasure-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_history_erasure.py')),
    ('numeric-history-erasure-kernel-controls', ('python3', 'scripts/check_history_erasure_controls.py')),
    ('numeric-clean-argument-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_clean_arguments.py')),
    ('numeric-clean-argument-kernel-controls', ('python3', 'scripts/check_clean_argument_controls.py')),
    ('numeric-lookup-source-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_lookup_source.py')),
    ('numeric-lookup-source-kernel-controls', ('python3', 'scripts/check_lookup_source_controls.py')),
    ('numeric-source-freshness-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_source_freshness.py')),
    ('numeric-source-freshness-kernel-controls', ('python3', 'scripts/check_source_freshness_controls.py')),
    ('numeric-worker-port-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_worker_ports.py')),
    ('numeric-worker-port-kernel-controls', ('python3', 'scripts/check_worker_port_controls.py')),
    ('numeric-helper-validity-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_helper_validity.py')),
    ('numeric-helper-validity-shared-controls', ('python3', 'scripts/check_helper_validity_controls.py', '--shared-only')),
    ('numeric-helper-validity-cached-controls', ('python3', 'scripts/check_helper_validity_controls.py', '--case', 'AddSubCached', '--case', 'JumpBranchCached', '--case', 'MulDivCached', '--case', 'ShiftBinopCached', '--case', 'WordMemoryCached', '--case', 'SubwordMemoryCached', '--case', 'UnifiedCached', '--case', 'BigintCached', '--case', 'BlakeGCached', '--case', 'BlakeRoundCached', '--case', 'KeccakCached')),
    ('numeric-helper-payload-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_helper_payload.py')),
    ('helper-history-projection-kernel-controls', ('python3', 'scripts/check_helper_history_projection_controls.py')),
    ('helper-projection-kernel-controls', ('python3', 'scripts/check_helper_projection_controls.py')),
    ('numeric-helper-payload-kernel-controls', ('python3', 'scripts/check_helper_payload_controls.py')),
    ('numeric-memory-payload-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_memory_payload.py')),
    ('numeric-memory-payload-shared-controls', ('python3', 'scripts/check_memory_payload_controls.py', '--shared-only')),
    ('numeric-memory-payload-cached-controls', ('python3', 'scripts/check_memory_payload_controls.py', '--case', 'AddSubCached', '--case', 'JumpBranchCached', '--case', 'MulDivCached', '--case', 'ShiftBinopCached', '--case', 'WordMemoryCached', '--case', 'SubwordMemoryCached', '--case', 'UnifiedCached', '--case', 'BigintCached', '--case', 'BlakeGCached', '--case', 'BlakeRoundCached', '--case', 'KeccakCached')),
    ('numeric-query-frame-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_query_frame.py')),
    ('numeric-query-frame-kernel-controls', ('python3', 'scripts/check_query_frame_controls.py')),
    ('packed-xor7-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_xor7.py')),
    ('packed-xor7-kernel-controls', ('python3', 'scripts/check_packed_xor7_controls.py')),
    ('fixed-special-generator-controls', ('python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_packed_special_spans.py')),
    ('packed-xor9-controls', ('python3', 'scripts/check_packed_xor9_controls.py')),
    ('packed-byte-controls', ('python3', 'scripts/check_packed_byte_table_controls.py')),
    ('packed-word-column-kernel-controls', ('python3', 'scripts/check_packed_word_column_controls.py')),
)


def run_command(command, label, args):
    if args.command != "validate":
        subprocess.run(command, cwd=LEAN, check=True)
        return
    args.logs.mkdir(parents=True, exist_ok=True)
    guard = [sys.executable, str(SCRIPTS / "bounded_fv.py"),
             "--mib", "2560", "--resident-mib", "5120", "--seconds", "900",
             "--log", str(args.logs / (label + ".log")), "--", *command]
    result = subprocess.run(guard, cwd=LEAN, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (args.logs / (label + ".guard.jsonl")).write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    reports = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
    reports = [entry for entry in reports if "reason" in entry]
    if (result.returncode or len(reports) != 1 or reports[0].get("reason") != "finished"
            or reports[0].get("exit") != 0 or reports[0].get("live_owned_after") != []):
        raise SystemExit("Checker framework command failed: " + label)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "all", "captures", "tables", "compiler", "validate"))
    parser.add_argument("--write", action="store_true", help="Write changed sources; source commands otherwise check freshness")
    parser.add_argument("--family", action="append", help="Limit the compiler export subcommand")
    parser.add_argument("--output", type=Path, help="Compiler export destination")
    parser.add_argument("--logs", type=Path, default=Path("/tmp/airbender-checker-framework"), help="Per-command final validation evidence")
    args = parser.parse_args()
    if args.command in ("check", "validate") and args.write:
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
    count = 0
    for group, script, options in GENERATORS:
        if args.command not in ("all", "check", "validate", group):
            continue
        command = [sys.executable, str(SCRIPTS / script), *options]
        command += ([] if script in WRITE_BY_DEFAULT else ["--write"]) if args.write else ["--check"]
        print(("GENERATE" if args.write else "FRESHNESS") + " " + script, flush=True)
        run_command(command, "freshness-" + str(count) + "-" + script.removesuffix(".py"), args)
        count += 1
    print(f"PASS {count} cached verification source generators", flush=True)
    if args.command == "validate":
        for label, command in CONTROLS:
            command = [sys.executable if value == "python3" and index == 0 else value
                       for index, value in enumerate(command)]
            print("CONTROL " + label, flush=True)
            run_command(command, label, args)
        print(f"PASS {len(CONTROLS)} final checker framework controls", flush=True)

if __name__ == "__main__":
    main()
